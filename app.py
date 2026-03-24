"""
Gmail Data Extractor — Final Production Version
Fixes applied:
  1. Advanced filters  — date range + sender filter
  2. Pagination        — page-based with configurable page size
  3. Cleaner extraction — stricter phone/link/amount cleaning
  4. Auth persistence  — token saved to disk, auto-reloaded on restart
"""

import base64
import csv
import io
import json
import os
import re
import secrets
import unicodedata
from datetime import datetime, timedelta
from html import unescape
from pathlib import Path

from flask import (
    Flask,
    Response,
    jsonify,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from google.auth.transport.requests import Request
from google_auth_oauthlib.flow import Flow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
import google.oauth2.credentials
from markupsafe import Markup, escape

# ──────────────────────────────────────────────────────────────
# Configuration
# ──────────────────────────────────────────────────────────────
BASE_DIR             = Path(__file__).resolve().parent
CLIENT_SECRETS_FILE  = BASE_DIR / "credentials.json"
TOKEN_DIR            = BASE_DIR / ".tokens"          # FIX 4: persistent token folder
SCOPES               = ["https://www.googleapis.com/auth/gmail.readonly"]
REDIRECT_URI         = "http://127.0.0.1:5000/oauth2callback"
PAGE_SIZE            = 10                             # FIX 2: results per page

app = Flask(__name__)

_secret = os.environ.get("FLASK_SECRET_KEY", "").strip()
if not _secret:
    raise RuntimeError(
        "FLASK_SECRET_KEY environment variable is not set.\n"
        "Run:  export FLASK_SECRET_KEY=$(python -c \"import secrets; print(secrets.token_hex(32))\")\n"
        "Then restart the app."
    )
app.secret_key = _secret

if os.environ.get("ALLOW_INSECURE_OAUTH_TRANSPORT") == "1":
    os.environ["OAUTHLIB_INSECURE_TRANSPORT"] = "1"

TOKEN_DIR.mkdir(exist_ok=True)

# ──────────────────────────────────────────────────────────────
# Score weights
# ──────────────────────────────────────────────────────────────
SCORE_WEIGHTS = {"subject": 10, "from": 6, "snippet": 4, "body": 2}

# ──────────────────────────────────────────────────────────────
# Junk-link patterns
# ──────────────────────────────────────────────────────────────
JUNK_LINK_RE = re.compile(
    r"(unsubscribe|tracking|pixel|beacon|open\.php|click\.php|"
    r"utm_|mailtrack|list-manage|sendgrid|mailchimp|"
    r"\.png$|\.jpg$|\.gif$|\.ico$|\.woff$|"
    r"r\.mail\.|click\.|email\.|links\.|go\.)",
    re.IGNORECASE,
)
MAX_LINK_LEN = 120


# ──────────────────────────────────────────────────────────────
# FIX 4 — Persistent token helpers (disk-based)
# ──────────────────────────────────────────────────────────────

def _token_path(session_id: str) -> Path:
    safe = re.sub(r"[^A-Za-z0-9_-]", "_", session_id)
    return TOKEN_DIR / f"{safe}.json"


def save_token(session_id: str, cred_data: dict) -> None:
    with open(_token_path(session_id), "w") as f:
        json.dump(cred_data, f)


def load_token(session_id: str) -> dict | None:
    path = _token_path(session_id)
    if not path.exists():
        return None
    try:
        with open(path) as f:
            return json.load(f)
    except Exception:
        return None


def delete_token(session_id: str) -> None:
    path = _token_path(session_id)
    if path.exists():
        path.unlink()


# ──────────────────────────────────────────────────────────────
# Session helpers
# ──────────────────────────────────────────────────────────────

def get_session_id() -> str:
    sid = session.get("session_id")
    if not sid:
        sid = secrets.token_urlsafe(24)
        session["session_id"] = sid
    return sid


def clear_session_state() -> None:
    sid = session.get("session_id")
    if sid:
        delete_token(sid)
    session.clear()


# ──────────────────────────────────────────────────────────────
# Text normalisation
# ──────────────────────────────────────────────────────────────

def normalize_unicode(text: str) -> str:
    return unicodedata.normalize("NFC", text or "")


def normalize_text(text: str) -> str:
    text = normalize_unicode(text or "").strip().casefold()
    return re.sub(r"\s+", " ", text)


def contains_non_ascii(text: str) -> bool:
    return any(ord(c) > 127 for c in (text or ""))


# ──────────────────────────────────────────────────────────────
# Keyword helpers
# ──────────────────────────────────────────────────────────────

def parse_keywords(raw: str) -> list[str]:
    if not raw:
        return []
    seen, out = set(), []
    for item in raw.split(","):
        kw = normalize_text(item)
        if kw and kw not in seen:
            seen.add(kw)
            out.append(kw)
    return out


def keyword_pattern(keyword: str):
    keyword = (keyword or "").strip()
    if not keyword:
        return None
    if contains_non_ascii(keyword):
        return re.compile(re.escape(normalize_unicode(keyword)), re.IGNORECASE)
    if " " in keyword:
        escaped = re.escape(keyword).replace(r"\ ", r"\s+")
        return re.compile(escaped, re.IGNORECASE)
    return re.compile(rf"\b{re.escape(keyword)}\b", re.IGNORECASE)


def keyword_in_text(keyword: str, text: str) -> bool:
    pat = keyword_pattern(keyword)
    if not pat or not text:
        return False
    return pat.search(normalize_unicode(text)) is not None


def get_matched_keywords(keywords: list[str], text: str) -> list[str]:
    return [kw for kw in keywords if keyword_in_text(kw, text)]


# ──────────────────────────────────────────────────────────────
# FIX 1 — Advanced filter helpers (date range + sender)
# ──────────────────────────────────────────────────────────────

def build_gmail_query(keywords: list[str], sender_filter: str,
                      date_from: str, date_to: str) -> str:
    """
    Build Gmail search query string.
    Gmail syntax:
      from:address          — sender filter
      after:YYYY/MM/DD      — from date (inclusive)
      before:YYYY/MM/DD     — to date (exclusive, so we add 1 day)
      "keyword"             — keyword pre-filter
    """
    parts = []

    if sender_filter and sender_filter.strip():
        parts.append(f"from:{sender_filter.strip()}")

    if date_from:
        try:
            d = datetime.strptime(date_from, "%Y-%m-%d")
            parts.append(f"after:{d.strftime('%Y/%m/%d')}")
        except ValueError:
            pass

    if date_to:
        try:
            d = datetime.strptime(date_to, "%Y-%m-%d") + timedelta(days=1)
            parts.append(f"before:{d.strftime('%Y/%m/%d')}")
        except ValueError:
            pass

    if keywords:
        parts.append(" OR ".join(f'"{kw}"' for kw in keywords))

    return " ".join(parts)


def _safe_page(raw) -> int:
    """Parse page number safely; always returns an integer >= 1."""
    try:
        return max(1, int(raw or 1))
    except (TypeError, ValueError):
        return 1


def parse_filter_args() -> dict:
    return {
        "sender_filter": request.args.get("sender", "").strip(),
        "date_from":     request.args.get("date_from", "").strip(),
        "date_to":       request.args.get("date_to", "").strip(),
        "page":          _safe_page(request.args.get("page")),
    }


# ──────────────────────────────────────────────────────────────
# Gmail message parsing
# ──────────────────────────────────────────────────────────────

def find_header(headers: list, name: str) -> str:
    for h in headers:
        if h.get("name", "").lower() == name.lower():
            return h.get("value", "")
    return ""


def collect_body_parts(payload: dict, mime_pref="text/plain") -> list[str]:
    parts_out = []
    mime_type = payload.get("mimeType", "")

    if mime_type == mime_pref:
        data = payload.get("body", {}).get("data")
        if data:
            parts_out.append(data)

    for part in payload.get("parts", []):
        parts_out.extend(collect_body_parts(part, mime_pref))

    if not parts_out and mime_type.startswith("text/"):
        data = payload.get("body", {}).get("data")
        if data:
            parts_out.append(data)

    return parts_out


def decode_payload(payload: dict) -> str:
    encoded_parts = collect_body_parts(payload, "text/plain")
    if not encoded_parts:
        encoded_parts = collect_body_parts(payload, "text/html")
    if not encoded_parts:
        return ""

    texts = []
    for part in encoded_parts:
        try:
            decoded = base64.urlsafe_b64decode(part.encode("utf-8"))
            text = decoded.decode("utf-8", errors="replace")
        except Exception:
            continue
        text = re.sub(r"<[^>]+>", " ", text)
        text = unescape(text)
        texts.append(text)

    return re.sub(r"\s+", " ", " ".join(texts)).strip()


# ──────────────────────────────────────────────────────────────
# FIX 3 — Stricter extraction cleaning
# ──────────────────────────────────────────────────────────────

def _clean_phones(raw: list[str]) -> list[str]:
    """
    Valid phone: 7–15 digits (ITU-T E.164 max = 15).
    Reject 4-digit year-like strings (1900–2099).
    """
    year_re = re.compile(r"^(19|20)\d{2}$")
    seen, out = set(), []
    for p in raw:
        digits = re.sub(r"\D", "", p)
        if not (7 <= len(digits) <= 15):
            continue
        if year_re.match(digits):
            continue
        p = p.strip()
        if p not in seen:
            seen.add(p)
            out.append(p)
    return out[:5]


def _clean_links(raw: list[str]) -> list[str]:
    """
    Remove tracking/pixel/unsubscribe/image links.
    Remove bare IP addresses and links longer than MAX_LINK_LEN.
    """
    out, seen = [], set()
    for link in raw:
        link = link.rstrip(".,);>\"'")
        if len(link) > MAX_LINK_LEN:
            continue
        if JUNK_LINK_RE.search(link):
            continue
        if re.search(r"https?://\d+\.\d+\.\d+\.\d+", link):
            continue
        if link not in seen:
            seen.add(link)
            out.append(link)
    return out[:5]


def _clean_amounts(raw: list[str]) -> list[str]:
    """
    Keep amounts > 0. Accept max 2 decimal places. Collapse whitespace.
    """
    out, seen = [], set()
    for amt in raw:
        amt = re.sub(r"\s+", "", amt)
        digits = re.sub(r"[^\d.]", "", amt)
        try:
            val = float(digits or "0")
        except ValueError:
            continue
        if val <= 0:
            continue
        if "." in digits and len(digits.split(".")[1]) > 2:
            continue
        if amt not in seen:
            seen.add(amt)
            out.append(amt)
    return out[:5]


def extract_useful_fields(text: str) -> dict:
    emails = sorted(set(
        re.findall(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}", text)
    ))[:5]

    raw_phones = re.findall(
        r"(?:\+\d{1,3}[\s\-.])?(?:\(?\d{2,4}\)?[\s\-.]?)?\d{3}[\s\-.]?\d{4}",
        text,
    )
    phones = _clean_phones(raw_phones)

    dates = sorted(set(re.findall(
        r"\b(?:\d{1,2}[/\-.]){2}\d{2,4}\b"
        r"|\b(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*"
        r"[\s,.]+\d{1,2}[,\s]+\d{4}\b",
        text, re.IGNORECASE,
    )))[:5]

    raw_amounts = re.findall(
        r"(?:USD|INR|EUR|GBP|\$|€|£|Rs\.?|₹)\s?\d[\d,]*(?:\.\d{1,2})?",
        text, re.IGNORECASE,
    )
    amounts = _clean_amounts(raw_amounts)

    raw_links = re.findall(r"https?://[^\s<>\"']+", text)
    links = _clean_links(raw_links)

    return {"emails": emails, "phones": phones, "dates": dates,
            "amounts": amounts, "links": links}


# ──────────────────────────────────────────────────────────────
# Relevance scoring
# ──────────────────────────────────────────────────────────────

def compute_score(keywords, subject, sender, snippet, body) -> int:
    score = 0
    fields = {"subject": subject, "from": sender, "snippet": snippet, "body": body}
    for field, text in fields.items():
        weight = SCORE_WEIGHTS[field]
        for kw in keywords:
            if keyword_in_text(kw, text):
                score += weight
                if field == "body":
                    pat = keyword_pattern(kw)
                    if pat:
                        extra = len(pat.findall(normalize_unicode(text))) - 1
                        score += min(extra, 5)
    return score


# ──────────────────────────────────────────────────────────────
# Highlighting
# ──────────────────────────────────────────────────────────────

def highlight_text(text: str, keywords: list[str]) -> Markup:
    if not text:
        return Markup("")
    if not keywords:
        return escape(text)

    ranges = []
    for kw in keywords:
        pat = keyword_pattern(kw)
        if not pat:
            continue
        for m in pat.finditer(normalize_unicode(text)):
            ranges.append((m.start(), m.end()))

    if not ranges:
        return escape(text)

    ranges.sort()
    merged = []
    for s, e in ranges:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)

    parts, last = [], 0
    for s, e in merged:
        parts.append(escape(text[last:s]))
        parts.append(Markup("<mark>") + escape(text[s:e]) + Markup("</mark>"))
        last = e
    parts.append(escape(text[last:]))
    return Markup("").join(parts)


def build_body_excerpt(body: str, body_matches: list[str], window: int = 280) -> str:
    if not body:
        return ""
    if not body_matches:
        return body[:window].strip()
    for kw in body_matches:
        pat = keyword_pattern(kw)
        if not pat:
            continue
        m = pat.search(normalize_unicode(body))
        if m:
            s = max(0, m.start() - window // 2)
            e = min(len(body), m.end() + window // 2)
            excerpt = body[s:e].strip()
            if s > 0:
                excerpt = "…" + excerpt
            if e < len(body):
                excerpt += "…"
            return excerpt
    return body[:window].strip()


# ──────────────────────────────────────────────────────────────
# Build single email result
# ──────────────────────────────────────────────────────────────

def build_email_result(msg_data: dict, keywords: list[str]) -> dict | None:
    payload = msg_data.get("payload", {})
    headers = payload.get("headers", [])

    subject = find_header(headers, "Subject") or "(No subject)"
    sender  = find_header(headers, "From")    or "Unknown sender"
    date    = find_header(headers, "Date")    or "Unknown date"
    snippet = msg_data.get("snippet", "")     or "No preview available."
    body    = decode_payload(payload)

    subj_m = get_matched_keywords(keywords, subject) if keywords else []
    from_m = get_matched_keywords(keywords, sender)  if keywords else []
    snip_m = get_matched_keywords(keywords, snippet) if keywords else []
    body_m = get_matched_keywords(keywords, body)    if keywords else []

    all_matches = list(dict.fromkeys(subj_m + from_m + snip_m + body_m))

    if keywords and not all_matches:
        return None

    match_sources = (
        (["Subject"] if subj_m else []) +
        (["From"]    if from_m else []) +
        (["Snippet"] if snip_m else []) +
        (["Body"]    if body_m else [])
    )

    score        = compute_score(keywords, subject, sender, snippet, body)
    extracted    = extract_useful_fields(" ".join([subject, sender, snippet, body]))
    body_excerpt = build_body_excerpt(body, body_m)

    return {
        "subject":          highlight_text(subject, subj_m),
        "from":             highlight_text(sender,  from_m),
        "date":             date,
        "snippet":          highlight_text(snippet, snip_m),
        "body_excerpt":     highlight_text(body_excerpt, body_m) if body_m else "",
        "matched_keywords": all_matches,
        "match_sources":    match_sources,
        "extracted_fields": extracted,
        "relevance_score":  score,
        "export_data": {
            "subject":          subject,
            "from":             sender,
            "date":             date,
            "snippet":          snippet,
            "matched_keywords": all_matches,
            "match_sources":    match_sources,
            "relevance_score":  score,
            "extracted_fields": extracted,
        },
    }


# ──────────────────────────────────────────────────────────────
# FIX 2 — Paginated Gmail fetch
# ──────────────────────────────────────────────────────────────

def fetch_matching_emails(
    service,
    keywords:      list[str],
    sender_filter: str = "",
    date_from:     str = "",
    date_to:       str = "",
    page:          int = 1,
    page_size:     int = PAGE_SIZE,
    max_scan:      int = 200,
) -> dict:
    """
    Returns dict:
      emails       — list for current page
      page         — current page number
      total_found  — total matched results (pre-pagination)
      has_next     — bool
      has_prev     — bool
    """
    query = build_gmail_query(keywords, sender_filter, date_from, date_to)

    list_result = service.users().messages().list(
        userId="me",
        maxResults=max_scan,
        q=query if query else None,
    ).execute()

    all_candidates = []
    for message in list_result.get("messages", []):
        msg_data = service.users().messages().get(
            userId="me",
            id=message["id"],
            format="full",
        ).execute()
        result = build_email_result(msg_data, keywords)
        if result is None:
            continue
        all_candidates.append(result)

    all_candidates.sort(key=lambda r: r["relevance_score"], reverse=True)

    total_found = len(all_candidates)
    start       = (page - 1) * page_size
    end         = start + page_size

    return {
        "emails":      all_candidates[start:end],
        "page":        page,
        "total_found": total_found,
        "has_next":    end < total_found,
        "has_prev":    page > 1,
    }


# ──────────────────────────────────────────────────────────────
# FIX 4 — Gmail service (disk token, survives restart)
# ──────────────────────────────────────────────────────────────

def get_gmail_service():
    sid       = get_session_id()
    cred_data = load_token(sid)       # load from disk
    if not cred_data:
        return None

    creds = google.oauth2.credentials.Credentials(**cred_data)

    if creds.expired and creds.refresh_token:
        creds.refresh(Request())
        save_token(sid, {
            "token":         creds.token,
            "refresh_token": creds.refresh_token,
            "token_uri":     creds.token_uri,
            "client_id":     creds.client_id,
            "client_secret": creds.client_secret,
            "scopes":        creds.scopes,
        })

    return build("gmail", "v1", credentials=creds)


def fetch_export_payload(keywords, sender_filter="", date_from="", date_to="") -> list[dict]:
    service = get_gmail_service()
    if service is None:
        raise RuntimeError("Gmail service is not authenticated.")
    result = fetch_matching_emails(
        service, keywords, sender_filter, date_from, date_to,
        page=1, page_size=500, max_scan=500,
    )
    return [e["export_data"] for e in result["emails"]]


# ──────────────────────────────────────────────────────────────
# Error helper
# ──────────────────────────────────────────────────────────────

def parse_http_error(exc) -> dict:
    text = (
        exc.content.decode("utf-8", errors="ignore")
        if getattr(exc, "content", None) else str(exc)
    )
    if "SERVICE_DISABLED" in text or "has not been used in project" in text:
        return {
            "title":  "Gmail API is not enabled for this Google Cloud project",
            "message": text,
            "setup_steps": [
                "Enable the Gmail API in the same Google Cloud project as credentials.json.",
                "Verify the OAuth consent screen is configured for that project.",
                "Wait a few minutes after enabling, then retry.",
            ],
        }
    return {"title": "Google API request failed", "message": text, "setup_steps": []}


# ──────────────────────────────────────────────────────────────
# Routes
# ──────────────────────────────────────────────────────────────

@app.route("/")
def home():
    return render_template("index.html", keywords=session.get("keywords", ""))


@app.route("/login")
def login():
    raw_keywords = request.args.get("keywords", "").strip()
    clear_session_state()
    get_session_id()
    session["keywords"] = raw_keywords

    flow = Flow.from_client_secrets_file(
        str(CLIENT_SECRETS_FILE), scopes=SCOPES, redirect_uri=REDIRECT_URI,
    )
    authorization_url, state = flow.authorization_url(
        access_type="offline", include_granted_scopes="true", prompt="consent",
    )
    session["state"]         = state
    session["code_verifier"] = flow.code_verifier
    return redirect(authorization_url)


@app.route("/logout")
def logout():
    clear_session_state()
    return redirect(url_for("home"))


@app.route("/oauth2callback")
def oauth2callback():
    try:
        if "state" not in session or "code_verifier" not in session:
            raise ValueError("OAuth session state is missing or expired. Start login again.")

        flow = Flow.from_client_secrets_file(
            str(CLIENT_SECRETS_FILE), scopes=SCOPES,
            state=session["state"], redirect_uri=REDIRECT_URI,
        )
        flow.code_verifier = session["code_verifier"]
        flow.fetch_token(authorization_response=request.url)

        creds = flow.credentials
        save_token(get_session_id(), {        # FIX 4: save to disk
            "token":         creds.token,
            "refresh_token": creds.refresh_token,
            "token_uri":     creds.token_uri,
            "client_id":     creds.client_id,
            "client_secret": creds.client_secret,
            "scopes":        creds.scopes,
        })
        session.pop("state", None)
        session.pop("code_verifier", None)

    except Exception as exc:
        return render_template(
            "results.html",
            emails=[], keywords=parse_keywords(session.get("keywords", "")),
            error_title="OAuth flow failed", error_message=str(exc),
            setup_steps=[
                f"Confirm the redirect URI in Google Cloud is exactly {REDIRECT_URI}.",
                "Confirm credentials.json belongs to the correct Google Cloud project.",
                "If you used localhost before, also add 127.0.0.1 to Authorized redirect URIs.",
            ],
            page=1, total_found=0, has_next=False, has_prev=False,
            sender_filter="", date_from="", date_to="",
        )

    return redirect(url_for("emails"))


@app.route("/emails")
def emails():
    raw_keywords        = request.args.get("keywords", session.get("keywords", ""))
    keywords            = parse_keywords(raw_keywords)
    session["keywords"] = raw_keywords
    filters             = parse_filter_args()

    service = get_gmail_service()
    if service is None:
        return redirect(url_for("home"))

    try:
        result = fetch_matching_emails(
            service, keywords,
            sender_filter = filters["sender_filter"],
            date_from     = filters["date_from"],
            date_to       = filters["date_to"],
            page          = filters["page"],
        )

        return render_template(
            "results.html",
            emails        = result["emails"],
            keywords      = keywords,
            page          = result["page"],
            total_found   = result["total_found"],
            has_next      = result["has_next"],
            has_prev      = result["has_prev"],
            sender_filter = filters["sender_filter"],
            date_from     = filters["date_from"],
            date_to       = filters["date_to"],
            error_title   = None,
            error_message = None,
            setup_steps   = [],
        )

    except HttpError as exc:
        err = parse_http_error(exc)
        return render_template(
            "results.html", emails=[], keywords=keywords,
            error_title=err["title"], error_message=err["message"],
            setup_steps=err["setup_steps"],
            page=1, total_found=0, has_next=False, has_prev=False,
            sender_filter="", date_from="", date_to="",
        )

    except Exception as exc:
        return render_template(
            "results.html", emails=[], keywords=keywords,
            error_title="Unexpected application error", error_message=str(exc),
            setup_steps=[
                "Restart the Flask app and repeat the login flow.",
                "Verify credentials.json exists beside app.py.",
            ],
            page=1, total_found=0, has_next=False, has_prev=False,
            sender_filter="", date_from="", date_to="",
        )


@app.route("/export")
def export():
    if get_gmail_service() is None:
        return redirect(url_for("home"))

    keywords = parse_keywords(request.args.get("keywords", session.get("keywords", "")))
    sender   = request.args.get("sender", "")
    d_from   = request.args.get("date_from", "")
    d_to     = request.args.get("date_to", "")

    try:
        payload = fetch_export_payload(keywords, sender, d_from, d_to)
        return jsonify({
            "keywords": keywords,
            "filters":  {"sender": sender, "date_from": d_from, "date_to": d_to},
            "count":    len(payload),
            "data":     payload,
            "note":     "Processed temporarily. Not stored permanently by this application.",
        })
    except HttpError as exc:
        err = parse_http_error(exc)
        return jsonify({"error": err["title"], "message": err["message"],
                        "setup_steps": err["setup_steps"]}), 500
    except Exception as exc:
        return jsonify({"error": "Unexpected error", "message": str(exc)}), 500


@app.route("/export/csv")
def export_csv():
    if get_gmail_service() is None:
        return redirect(url_for("home"))

    keywords = parse_keywords(request.args.get("keywords", session.get("keywords", "")))
    sender   = request.args.get("sender", "")
    d_from   = request.args.get("date_from", "")
    d_to     = request.args.get("date_to", "")

    try:
        payload = fetch_export_payload(keywords, sender, d_from, d_to)

        output = io.StringIO()
        writer = csv.writer(output)
        writer.writerow([
            "Relevance Score", "Subject", "From", "Date",
            "Matched Keywords", "Match Sources",
            "Extracted Emails", "Extracted Phones",
            "Extracted Dates",  "Extracted Amounts",
            "Extracted Links",  "Snippet",
        ])
        for email in payload:
            ef = email.get("extracted_fields", {})
            writer.writerow([
                email.get("relevance_score", 0),
                email.get("subject", ""),
                email.get("from", ""),
                email.get("date", ""),
                ", ".join(email.get("matched_keywords", [])),
                ", ".join(email.get("match_sources", [])),
                ", ".join(ef.get("emails",  [])),
                ", ".join(ef.get("phones",  [])),
                ", ".join(ef.get("dates",   [])),
                ", ".join(ef.get("amounts", [])),
                ", ".join(ef.get("links",   [])),
                email.get("snippet", ""),
            ])

        csv_data = output.getvalue()
        output.close()

        return Response(
            csv_data, mimetype="text/csv",
            headers={"Content-Disposition": "attachment; filename=gmail_extraction_results.csv"},
        )

    except HttpError as exc:
        err = parse_http_error(exc)
        return jsonify({"error": err["title"], "message": err["message"],
                        "setup_steps": err["setup_steps"]}), 500
    except Exception as exc:
        return jsonify({"error": "Unexpected error", "message": str(exc)}), 500


if __name__ == "__main__":
    app.run(debug=True)