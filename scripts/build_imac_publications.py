"""Build affiliation-verified IMAC publication previews from ORCID/ADS CSVs.

Evidence order: NASA ADS -> OpenAlex -> arXiv author data -> paper PDF.
Missing evidence is not evidence of a non-IMAC affiliation.

Default: write docs/imac_affiliation_preview, never overwrite live tables.
The individual researchers' career-publication CSVs are read, not modified.
Optional manual decisions are matched by DOI, arXiv ID or exact normalized title.
The public summary always uses Shun's exact wording, with enlarged counts.
"""

import csv
import html
import ipaddress
import json
import os
import re
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from datetime import datetime, timezone
from difflib import SequenceMatcher
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote, unquote, urlencode, urlsplit
from urllib.request import Request, urlopen

import pymupdf

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "docs" / "publications"
LIVE_DIR = ROOT / "docs" / "imac"
PREVIEW_DIR = ROOT / "docs" / "imac_affiliation_preview"
CACHE_FILE = PREVIEW_DIR / "affiliation_cache.json"
AUTHOR_CACHE_FILE = PREVIEW_DIR / "author_metadata_cache.json"
DECISIONS_FILE = ROOT / "affiliation_decisions.json"  # optional, evidence-based
RESEARCHERS_FILE = ROOT / "researchers.json"
ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"
ARXIV_API = "https://export.arxiv.org/api/query"
START_YEAR = 2019  # inclusive
MODE = os.getenv("IMAC_OUTPUT_MODE", "preview").strip().lower()
MAX_CHECKS = int(os.getenv("IMAC_MAX_NEW_CHECKS", "30"))
# New no-key author lookups per run (separate from the affiliation-check limit).
MAX_AUTHOR_LOOKUPS = max(0, int(os.getenv("IMAC_MAX_AUTHOR_LOOKUPS", "8")))
MAX_PDF_BYTES = 40 * 1024 * 1024
CACHE_VERSION = 4  # retry previously unresolved papers with full-PDF checks
PRIORITY_ARXIV = "2507.16707"  # ONLY processing priority, NOT automatic inclusion
USER_AGENT = "IMAC-MissouriST-Publications/2.0 (institutional bibliography)"
CSV_COLUMNS = ["Title", "Authors", "Journal", "Citation (ADS)", "DOI URL", "ADS URL"]
AUDIT_COLUMNS = ["Year", "Title", "Status", "Source", "Evidence", "Evidence URL",
                 "arXiv", "DOI URL", "ADS URL"]
ATOM = "{http://www.w3.org/2005/Atom}"
ARXIV_NS = "{http://arxiv.org/schemas/atom}"
LAST_ARXIV_REQUEST = 0.0
ADS_RATE_LIMITED = False
HISTORIC_AUDIT = {}

AFFILIATION_PATTERNS = [
    re.compile(r"\bMissouri\s+University\s+of\s+Science\s*(?:and|&)\s*Technology\b", re.I),
    re.compile(r"\bMissouri\s+S\s*(?:&|and)\s*T\b", re.I),
    re.compile(r"\bInstitute\s+for\s+Multi[\s-]*messenger\s+Astrophysics\s*(?:and|&)\s*Cosmology\b", re.I),
]
ARXIV_PATTERN = re.compile(
    r"(?i)(?:arxiv(?:\.org/(?:abs|pdf)/|[:./\s])|10\.48550/arxiv\.)"
    r"(\d{4}\.\d{4,5})(?:v\d+)?"
)
ARXIV_BIB_PATTERN = re.compile(r"\d{4}arXiv(\d{4})(\d{4,5})", re.I)
AFFILIATION_HEADING = re.compile(
    r"(?im)^\s*(?:author\s+)?affiliations?(?:\s+of\s+(?:the\s+)?authors)?\s*[:.]?\s*$"
)
ABSTRACT_HEADING = re.compile(r"(?im)^\s*(?:abstract|1\s*\.?\s*introduction)\s*$")
SECTION_HEADING = re.compile(
    r"(?im)^\s*(?:references|bibliography|acknowledg(?:e)?ments?|appendix)\s*$"
)


def clean(value):
    return html.unescape(html.unescape(str(value or ""))).strip()


def normalized_title(value):
    text = unicodedata.normalize("NFKD", clean(value)).casefold()
    text = text.replace(r"\alpha", "alpha").replace("α", "alpha")
    text = text.replace(r"\beta", "beta").replace("β", "beta")
    return re.sub(r"[^a-z0-9]", "", text)


def doi_key(value):
    value = re.sub(r"^https?://(?:dx\.)?doi\.org/", "", clean(value), flags=re.I)
    return unquote(re.sub(r"^doi:\s*", "", value, flags=re.I)).casefold()


def bibcode(value):
    match = re.search(r"/abs/([^/?#]+)", clean(value))
    return unquote(match.group(1)) if match else ""


def normalize_affiliation(text):
    text = clean(text)
    # Rejoin words split at PDF line breaks, e.g., "Technol-\nogy".
    text = re.sub(r"(?<=[a-zA-Z])-\s*\n\s*(?=[a-zA-Z])", "", text)
    return re.sub(r"\s+", " ", text)


def qualifying_affiliation(text):
    text = normalize_affiliation(text)
    return any(pattern.search(text) for pattern in AFFILIATION_PATTERNS)


def paper_title_matches(expected, candidate):
    a, b = normalized_title(expected), normalized_title(candidate)
    if min(len(a), len(b)) < 24:
        return a == b
    return SequenceMatcher(None, a, b).ratio() >= 0.91


def is_preprint(row):
    return ("arxiv" in row["Journal"].casefold()
            or row["doi_key"].startswith("10.48550/arxiv.")
            or row["Title"].casefold().startswith("arxiv:"))


def load_records():
    researchers = json.loads(RESEARCHERS_FILE.read_text(encoding="utf-8"))["researchers"]
    records = []
    for person in researchers:
        path = SOURCE / f'{person["orcid"]}.csv'
        if not path.is_file():
            raise FileNotFoundError(f"Researcher CSV missing: {path}")
        with path.open(newline="", encoding="utf-8-sig") as handle:
            reader = csv.DictReader(handle)
            cols = set(reader.fieldnames or [])
            if not {"Year", "Title", "Journal", "DOI URL", "ADS URL"}.issubset(cols):
                raise ValueError(f"Invalid CSV columns: {path}")
            if not ({"Citation (ADS)", "Citations"} & cols):
                raise ValueError(f"Citation column missing: {path}")
            for row in reader:
                year, title = clean(row.get("Year")), clean(row.get("Title"))
                if len(year) != 4 or not year.isdigit() or not title:
                    continue
                row.update({
                    "Year": year, "Title": title, "Journal": clean(row.get("Journal")),
                    "Citation (ADS)": clean(row.get("Citation (ADS)") or row.get("Citations")),
                    "doi_key": doi_key(row.get("DOI URL")),
                    "bibcode": bibcode(row.get("ADS URL")),
                    "title_key": normalized_title(title), "researcher": person["name"],
                })
                row["preprint"] = is_preprint(row)
                records.append(row)
    if not records:
        raise RuntimeError("No researcher publications were found")
    return researchers, records


def same_paper(row, cluster):
    if row["doi_key"] and row["doi_key"] in cluster["dois"]:
        return True
    if row["bibcode"] and row["bibcode"] in cluster["bibcodes"]:
        return True
    key = row["title_key"]
    if len(key) < 35:
        return False
    for other in cluster["records"]:
        if abs(int(row["Year"]) - int(other["Year"])) > 2:
            continue
        second = other["title_key"]
        if key == second:
            return True
        if (len(second) >= 35 and re.findall(r"\d+", key) == re.findall(r"\d+", second)
                and SequenceMatcher(None, key, second).ratio() >= 0.985):
            return True
    return False


def collapse(records):
    groups = []
    for row in records:
        group = next((g for g in groups if same_paper(row, g)), None)
        if group is None:
            group = {"records": [], "researchers": set(), "dois": set(), "bibcodes": set()}
            groups.append(group)
        group["records"].append(row)
        group["researchers"].add(row["researcher"])
        if row["doi_key"]:
            group["dois"].add(row["doi_key"])
        if row["bibcode"]:
            group["bibcodes"].add(row["bibcode"])
    return groups


def preferred_record(rows):
    def rank(row):
        value = row["Citation (ADS)"]
        return (not row["preprint"], bool(row["Journal"]), bool(row["doi_key"]),
                bool(row["bibcode"]), int(value) if value.isdigit() else -1)
    return max(rows, key=rank)


def is_priority(group):
    return any(PRIORITY_ARXIV in " ".join(clean(row.get(key)) for key in
               ("Title", "ADS URL", "DOI URL")) or
               ("simulatingrealistic" in row["title_key"] and
                "radiativetransfer" in row["title_key"] and
                "lyman" in row["title_key"])
               for row in group["records"])


def format_error(exc):
    if isinstance(exc, HTTPError):
        return f"HTTP {exc.code}"
    return f"{type(exc).__name__}: {str(exc)[:100]}"


def safe_public_https(url):
    parts = urlsplit(url)
    if parts.scheme != "https" or not parts.hostname or parts.username:
        return False
    hostname = parts.hostname.casefold()
    if hostname in {"localhost", "localhost.localdomain"} or hostname.endswith(".local"):
        return False
    try:
        if not ipaddress.ip_address(hostname).is_global:
            return False
    except ValueError:
        pass  # Hostname; external service provided this URL.
    return True


def wait_for_arxiv():
    global LAST_ARXIV_REQUEST
    if LAST_ARXIV_REQUEST:
        remaining = 3.2 - (time.monotonic() - LAST_ARXIV_REQUEST)
        if remaining > 0:
            time.sleep(remaining)
    LAST_ARXIV_REQUEST = time.monotonic()


def http_read(url, max_bytes=1_000_000, timeout=35, arxiv=False, headers=None):
    if not safe_public_https(url):
        raise ValueError("Invalid or unsafe HTTPS URL")
    request_headers = {"User-Agent": USER_AGENT}
    request_headers.update(headers or {})
    for attempt in range(3):
        if arxiv:
            wait_for_arxiv()
        try:
            with urlopen(Request(url, headers=request_headers), timeout=timeout) as response:
                if not safe_public_https(response.geturl()):
                    raise ValueError("Unsafe response URL")
                raw = response.read(max_bytes + 1)
            if len(raw) > max_bytes:
                raise ValueError(f"Response exceeds {max_bytes // (1024 * 1024)} MiB limit")
            return raw
        except (HTTPError, URLError, TimeoutError, ConnectionError) as exc:
            retryable = not isinstance(exc, HTTPError) or exc.code in {408, 429, 500, 502, 503, 504}
            if not retryable or attempt == 2:
                raise
            time.sleep(2 * (attempt + 1))
    raise RuntimeError("Unreachable request retry logic")


def load_historic_audit():
    """Previous successful verification results are read-only fallback evidence.

    We reuse only explicit `verified` records, matched by publication year
    and exact normalized title. An absence of such evidence does not prove
    that the paper should be excluded.
    """
    index = {}
    path = PREVIEW_DIR / "affiliation_audit.csv"
    if not path.is_file():
        return index
    with path.open(newline="", encoding="utf-8-sig") as handle:
        for row in csv.DictReader(handle):
            if row.get("Status") != "verified":
                continue
            year = clean(row.get("Year"))
            title = normalized_title(row.get("Title"))
            if year.isdigit() and title:
                index[(year, title)] = row
    return index


def previously_verified(group):
    for row in group["records"]:
        old = HISTORIC_AUDIT.get((str(row["Year"]), normalized_title(row["Title"])))
        if old:
            return old
    return None


def fetch_ads(records, token):
    """Query NASA ADS in batches; stop querying on HTTP 429.

    Preserve previously verified affiliations from the audit when ADS is
    unavailable. Never infer `excluded` from absent ADS records.
    """
    global ADS_RATE_LIMITED
    keys = sorted({("bibcode", row["bibcode"]) for row in records if row["bibcode"]})
    keys += sorted({("doi", row["doi_key"]) for row in records if row["doi_key"]})
    by_bibcode, by_doi = {}, {}
    for offset in range(0, len(keys), 15):
        parts = []
        for field, value in keys[offset:offset + 15]:
            escaped = value.replace("\\", "\\\\").replace('"', '\\"')
            parts.append(f'{field}:"{escaped}"')
        url = ADS_API + "?" + urlencode({
            "q": " OR ".join(parts),
            "fl": "bibcode,doi,identifier,first_author,author_count,aff,citation_count",
            "rows": 200,
        })
        try:
            raw = http_read(url, max_bytes=8_000_000, timeout=75,
                            headers={"Authorization": f"Bearer {token}", "Accept": "application/json"})
        except HTTPError as error:
            if error.code == 429:
                ADS_RATE_LIMITED = True
                print("WARNING: ADS returned HTTP 429. Remaining ADS batches skipped. "
                      "Using previously verified affiliation audit where available.")
                break
            raise
        response = json.loads(raw).get("response", {})
        docs = response.get("docs")
        if not isinstance(docs, list) or response.get("numFound", 0) > len(docs):
            raise RuntimeError("Truncated or malformed ADS response; no publication files updated")
        for doc in docs:
            if doc.get("bibcode"):
                by_bibcode[doc["bibcode"]] = doc
            identifiers = doc.get("doi") or []
            if isinstance(identifiers, str):
                identifiers = [identifiers]
            for identifier in identifiers:
                by_doi[doi_key(identifier)] = doc
    return by_bibcode, by_doi


def documents_for(group, ads):
    by_bibcode, by_doi = ads
    docs, seen = [], set()
    for row in group["records"]:
        for doc in (by_bibcode.get(row["bibcode"]), by_doi.get(row["doi_key"])):
            if doc:
                key = doc.get("bibcode") or id(doc)
                if key not in seen:
                    seen.add(key)
                    docs.append(doc)
    return docs


def check_ads(docs):
    for doc in docs:
        affs = doc.get("aff") or []
        if isinstance(affs, str):
            affs = [affs]
        for affiliation in affs:
            if qualifying_affiliation(affiliation):
                return normalize_affiliation(affiliation)[:300]
    return ""


def known_arxiv_id(group, docs):
    pieces = []
    for row in group["records"]:
        pieces.extend(clean(row.get(key)) for key in ("DOI URL", "ADS URL", "Title", "Journal"))
    for doc in docs:
        ids = doc.get("identifier") or []
        if isinstance(ids, str):
            ids = [ids]
        pieces += ids + [doc.get("bibcode", "")]
    for piece in pieces:
        match = ARXIV_PATTERN.search(str(piece))
        if match:
            return match.group(1)
        match = ARXIV_BIB_PATTERN.search(str(piece))
        if match:
            return f"{match.group(1)}.{match.group(2)}"
    return PRIORITY_ARXIV if is_priority(group) else ""


def parse_arxiv(raw):
    root = ET.fromstring(raw)
    entries = []
    for entry in root.findall(ATOM + "entry"):
        url = clean(entry.findtext(ATOM + "id"))
        match = ARXIV_PATTERN.search(url)
        if not match:
            continue
        title = clean(entry.findtext(ATOM + "title"))
        year_text = clean(entry.findtext(ATOM + "published"))
        year = int(year_text[:4]) if re.match(r"^\d{4}", year_text) else 0
        affs = []
        people = entry.findall(ATOM + "author")
        for author in people:
            affs += [normalize_affiliation(item.text) for item in author.findall(ARXIV_NS + "affiliation") if item.text]
        full_name = clean(people[0].findtext(ATOM + "name")) if people else ""
        first_author = full_name.split()[-1] if full_name else ""
        entries.append({"id": match.group(1), "title": title, "year": year,
                        "affiliations": affs, "first_author": first_author,
                        "author_count": len(people)})
    return entries


def arxiv_by_id(identifier, title):
    url = ARXIV_API + "?" + urlencode({"id_list": identifier, "max_results": 1})
    entries = parse_arxiv(http_read(url, max_bytes=800_000, arxiv=True))
    for entry in entries:
        if entry["id"] == identifier and paper_title_matches(title, entry["title"]):
            return entry
    return None


def arxiv_by_title(title, year):
    # A verified title match is required: never trust the first search result.
    words = re.findall(r"[a-zA-Z0-9]+", unicodedata.normalize("NFKD", title))
    if len(words) < 4:
        return None
    search_phrase = " ".join(words[:8]).replace('"', '')
    url = ARXIV_API + "?" + urlencode({
        "search_query": f'ti:"{search_phrase}"', "start": 0, "max_results": 10,
    })
    entries = parse_arxiv(http_read(url, max_bytes=1_500_000, arxiv=True))
    for entry in sorted(entries,
                        key=lambda e: SequenceMatcher(None, normalized_title(title),
                                                      normalized_title(e["title"])).ratio(),
                        reverse=True):
        if paper_title_matches(title, entry["title"]) and (not entry["year"] or abs(entry["year"] - year) <= 4):
            return entry
    return None


def lookup_openalex(group):
    # DOI is an exact identifier; no title-only OpenAlex guessing.
    dois = [row["doi_key"] for row in group["records"]
            if row["doi_key"] and not row["doi_key"].startswith("10.48550/arxiv.")]
    if not dois:
        return None
    doi = dois[0]
    url = "https://api.openalex.org/works/https://doi.org/" + quote(doi, safe="/")
    try:
        raw = http_read(url, max_bytes=3_000_000, timeout=30,
                        headers={"Accept": "application/json"})
    except HTTPError as exc:
        if exc.code == 404:
            return None  # DOI absent from OpenAlex is not a network failure.
        raise
    obj = json.loads(raw)
    # Guard against unexpectedly matching a different work.
    expected = preferred_record(group["records"])["Title"]
    if obj.get("title") and not paper_title_matches(expected, obj["title"]):
        return None
    return obj


def openalex_affiliation(obj):
    if not obj:
        return ""
    for author in obj.get("authorships") or []:
        for affiliation in author.get("raw_affiliation_strings") or []:
            if qualifying_affiliation(affiliation):
                return normalize_affiliation(affiliation)[:300]
        for inst in author.get("institutions") or []:
            institution = inst.get("display_name") or ""
            if qualifying_affiliation(institution):
                return institution[:300]
    return ""


def openalex_pdf_urls(obj):
    if not obj:
        return []
    locations = [obj.get("best_oa_location") or {}] + (obj.get("locations") or [])
    urls = []
    for location in locations:
        url = location.get("pdf_url") or ""
        if safe_public_https(url) and url not in urls:
            urls.append(url)
    return urls[:3]


def pdf_header_affiliation(url):
    """Check ALL PDF pages, but accept only author-affiliation evidence.

    Recognizes (a) pre-abstract bylines, (b) explicitly headed
    affiliation sections and (c) collaboration-style NUMBERED lists
    of institutions, even when the list is at the end of a paper.

    Do not treat an arbitrary mention in the main text, references,
    or acknowledgments as evidence of author affiliation.
    """

    raw = http_read(
        url,
        max_bytes=MAX_PDF_BYTES,
        timeout=65,
        arxiv="arxiv.org" in (urlsplit(url).hostname or ""),
        headers={"Accept": "application/pdf"},
    )
    if not raw.lstrip().startswith(b"%PDF"):
        raise ValueError("URL did not provide a readable PDF")

    # Numbered author-affiliation examples:
    #   109Kenyon College, Gambier, Ohio, USA
    #   110Missouri University of Science and Technology, Rolla, USA
    # or a superscript number on its own line followed by the institution.
    number_and_name = re.compile(
        r"^\s*(\d{1,4})(?!\d)(?:\s+|(?=[A-Za-z]))([A-Za-z].*)$"
    )
    number_only = re.compile(r"^\s*\d{1,4}\s*$")
    institution_word = re.compile(
        r"\b(?:university|universit\w*|college|institute|institut\w*|"
        r"laborator\w*|observator\w*|department|school|academy|"
        r"research\s+cent(?:er|re)|INFN|CNRS)\b",
        re.IGNORECASE,
    )

    def numbered_affiliation_match(page_text):
        """Find Missouri S&T in a dense numbered institution list."""
        lines = [line.strip() for line in page_text.splitlines() if line.strip()]
        entries = []
        for index, line in enumerate(lines):
            match = number_and_name.match(line)
            if match:
                beginning = match.group(2)
            elif number_only.match(line) and index + 1 < len(lines):
                beginning = lines[index + 1]
            else:
                continue

            # Allow a wrapped institution/address entry, stopping at
            # the NEXT numbered affiliation instead of merging records.
            continuation = []
            first_next = index + (2 if number_only.match(line) else 1)
            for next_line in lines[first_next:first_next + 3]:
                if number_and_name.match(next_line) or number_only.match(next_line):
                    break
                continuation.append(next_line)
            entry = normalize_affiliation(" ".join([beginning] + continuation))
            if institution_word.search(entry):
                entries.append(entry)

        # At least three numbered institutional entries distinguish an
        # author-affiliation list from an isolated numbered citation.
        if len(entries) < 3:
            return ""
        for entry in entries:
            if qualifying_affiliation(entry):
                return entry[:320]
        return ""

    with pymupdf.open(stream=raw, filetype="pdf") as document:
        in_affiliation_section = False
        front_matter = True

        # IMPORTANT: every page is examined, not just the first and last.
        for page_number in range(len(document)):
            text = document[page_number].get_text("text", sort=True)
            if not text.strip():
                continue

            # Collaboration author lists may be at the END of the PDF
            # and often have no 'Affiliations' heading at all.
            match = numbered_affiliation_match(text)
            if match:
                return match, f"{url}#page={page_number + 1}"

            candidates = []

            # Standard small-author papers: the byline precedes ABSTRACT.
            # Limit this method to the opening pages, not the full body.
            if front_matter and page_number < 3:
                abstract = ABSTRACT_HEADING.search(text)
                candidates.append(text[:abstract.start()] if abstract else text[:9000])
                if abstract:
                    front_matter = False
            else:
                front_matter = False

            # Explicitly labeled affiliation blocks may occur anywhere.
            heading = AFFILIATION_HEADING.search(text)
            if heading:
                in_affiliation_section = True
                candidates.append(text[heading.end():])
            elif in_affiliation_section:
                if SECTION_HEADING.search(text[:700]):
                    in_affiliation_section = False
                else:
                    candidates.append(text)

            for candidate in candidates:
                normalized = normalize_affiliation(candidate)
                for pattern in AFFILIATION_PATTERNS:
                    match = pattern.search(normalized)
                    if match:
                        excerpt = normalized[
                            max(0, match.start() - 70):match.end() + 130
                        ]
                        return excerpt[:320], f"{url}#page={page_number + 1}"

    return "", ""



def cluster_cache_key(group):
    row = preferred_record(group["records"])
    if row["doi_key"]:
        return "doi:" + row["doi_key"]
    if row["bibcode"]:
        return "ads:" + row["bibcode"]
    return "title:" + row["title_key"]


def load_cache():
    if CACHE_FILE.is_file():
        value = json.loads(CACHE_FILE.read_text(encoding="utf-8"))
        if isinstance(value, dict):
            return value
    return {}


def save_cache(cache):
    CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
    temporary = CACHE_FILE.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(cache, indent=2, sort_keys=True), encoding="utf-8")
    os.replace(temporary, CACHE_FILE)


def decision_title_key(title):
    """Exact, punctuation-insensitive title key; ignore display-only 'arXiv:' prefix."""
    title = re.sub(r"^\s*arxiv\s*:\s*", "", clean(title), flags=re.I)
    return normalized_title(title)


def manual_evidence_url(value):
    """Accept a plain HTTPS URL or a Markdown link copied from ChatGPT."""
    value = clean(value)
    markdown = re.fullmatch(r"\[(https://[^]\s]+)\]\((https://[^)\s]+)\)", value)
    if markdown:
        value = markdown.group(2)
    if not safe_public_https(value):
        raise ValueError(f"Manual decision evidence must be a public HTTPS URL: {value[:90]}")
    return value


def load_decisions():
    """Index optional manual reviews by every supplied DOI, arXiv ID and exact title.

    The original ORCID CSV often lacks arXiv IDs, so title matching is essential.
    Multiple lookup keys refer to the SAME decision, not to extra publications.
    """
    if not DECISIONS_FILE.is_file():
        print("No affiliation_decisions.json found: automated checks only.")
        return {}

    raw = json.loads(DECISIONS_FILE.read_text(encoding="utf-8"))
    if not isinstance(raw, dict) or not isinstance(raw.get("decisions"), list):
        raise ValueError("affiliation_decisions.json must contain a 'decisions' array")

    by_key = {}
    for number, original in enumerate(raw["decisions"], start=1):
        if not isinstance(original, dict):
            raise ValueError(f"Manual decision {number} must be an object")
        item = dict(original)
        if item.get("decision") not in {"include", "exclude"}:
            raise ValueError(f"Manual decision {number}: use include or exclude")
        if not clean(item.get("reason")):
            raise ValueError(f"Manual decision {number}: reason is required")
        item["evidence_url"] = manual_evidence_url(item.get("evidence_url"))
        item["_matched"] = False
        item["_row_number"] = number

        keys = []
        if item.get("doi"):
            doi = doi_key(item["doi"])
            if doi:
                keys.append("doi:" + doi)
            # arXiv DOIs such as 10.48550/arxiv.2306.12201 also identify arXiv papers.
            match = ARXIV_PATTERN.search(doi)
            if match:
                keys.append("arxiv:" + match.group(1))
        if item.get("arxiv"):
            match = re.search(r"(?:^|[^0-9])(\d{4}\.\d{4,5})(?:v\d+)?(?:$|[^0-9])",
                              clean(item["arxiv"]))
            if not match:
                raise ValueError(f"Manual decision {number}: invalid arXiv ID")
            keys.append("arxiv:" + match.group(1))
        if item.get("ads_bibcode"):
            keys.append("ads:" + clean(item["ads_bibcode"]))
        if item.get("title"):
            title = decision_title_key(item["title"])
            if len(title) < 15:
                raise ValueError(f"Manual decision {number}: title is too short")
            keys.append("title:" + title)
        if not keys:
            raise ValueError(f"Manual decision {number}: DOI, arXiv ID or title required")

        for key in set(keys):
            old = by_key.get(key)
            if old and old["decision"] != item["decision"]:
                raise ValueError(
                    f"Conflicting include/exclude decisions for {key}: "
                    f"entries {old['_row_number']} and {number}"
                )
            if old:
                raise ValueError(f"Duplicate manual decisions for {key}: entries "
                                 f"{old['_row_number']} and {number}")
            by_key[key] = item

    print(f"Loaded {len(raw['decisions'])} manual review decisions")
    return by_key


def check_decision(group, decisions, docs=None, identifier=""):
    """Apply a single decision to a deduplicated paper group, before auto checks.

    Only exact normalized titles and known identifiers are matched (no fuzzy
    matching here, to avoid applying an exclusion to the wrong publication).
    """
    if not decisions:
        return None

    keys = []
    for row in group["records"]:
        if row["doi_key"]:
            keys.append("doi:" + row["doi_key"])
            match = ARXIV_PATTERN.search(row["doi_key"])
            if match:
                keys.append("arxiv:" + match.group(1))
        if row["bibcode"]:
            keys.append("ads:" + row["bibcode"])
        keys.append("title:" + decision_title_key(row["Title"]))
        for field in ("DOI URL", "ADS URL", "Journal", "Title"):
            match = ARXIV_PATTERN.search(clean(row.get(field)))
            if match:
                keys.append("arxiv:" + match.group(1))
    if identifier:
        keys.append("arxiv:" + identifier)
    for doc in docs or []:
        code = clean(doc.get("bibcode"))
        if code:
            keys.append("ads:" + code)
        dois = doc.get("doi") or []
        if isinstance(dois, str):
            dois = [dois]
        for doi in dois:
            if isinstance(doi, str):
                keys.append("doi:" + doi_key(doi))
        identifiers = doc.get("identifier") or []
        if isinstance(identifiers, str):
            identifiers = [identifiers]
        for reference in identifiers:
            match = ARXIV_PATTERN.search(clean(reference))
            if match:
                keys.append("arxiv:" + match.group(1))

    matches = {id(decisions[key]): decisions[key] for key in set(keys) if key in decisions}
    if not matches:
        return None
    if len(matches) != 1:
        titles = [clean(item.get("title")) for item in matches.values()]
        raise ValueError(f"Several manual decisions matched the same paper: {titles}")

    item = next(iter(matches.values()))
    item["_matched"] = True
    return (
        "verified" if item["decision"] == "include" else "excluded",
        "manual review",
        clean(item["reason"])[:320],
        item["evidence_url"],
    )


def log_manual_coverage(decisions):
    """Report decisions that could not be applied to any currently imported work."""
    unique = {id(item): item for item in decisions.values()}
    used = sum(bool(item["_matched"]) for item in unique.values())
    print(f"Manual decision coverage: {used}/{len(unique)} matched a source publication")
    for item in unique.values():
        if not item["_matched"]:
            print(f"WARNING: manual decision not matched to ORCID source: "
                  f"{item.get('title') or item.get('doi') or item.get('arxiv')}")


def cached_result(old):
    if not isinstance(old, dict):
        return False
    # Preserve known positive matches; recheck old negative cache entries with v3 engine.
    if old.get("status") == "verified":
        return True
    if old.get("cache_version") != CACHE_VERSION:
        return False
    try:
        stamp = datetime.fromisoformat(old["checked_at"])
        age = (datetime.now(timezone.utc) - stamp).total_seconds() / 86400
    except (KeyError, ValueError, TypeError):
        return False
    days = 1 if old.get("status") == "error" else 30
    return age < days


def verify(group, ads, cache, decisions, budget):
    docs = documents_for(group, ads)
    identifier = known_arxiv_id(group, docs)
    override = check_decision(group, decisions, docs, identifier)
    if override:
        return (*override, identifier)

    hit = check_ads(docs)
    if hit:
        return "verified", "NASA ADS", hit, "", identifier

    # In an ADS-rate-limited run, retain the previously audited and verified
    # status. Manual exclusions above always take precedence over old audits.
    if ADS_RATE_LIMITED:
        previous = previously_verified(group)
        if previous:
            return ("verified", previous.get("Source", "prior verified audit"),
                    previous.get("Evidence", "Previously verified IMAC affiliation"),
                    previous.get("Evidence URL", ""),
                    identifier or previous.get("arXiv", ""))

    key = cluster_cache_key(group)
    old = cache.get(key, {})
    if cached_result(old):
        return (old["status"], old.get("source", "cached"), old.get("evidence", ""),
                old.get("evidence_url", ""), old.get("arxiv_id") or identifier)
    if budget["used"] >= MAX_CHECKS:
        return "pending", "budget", "Waiting for next daily run", "", identifier
    budget["used"] += 1

    title = preferred_record(group["records"])["Title"]
    year = int(preferred_record(group["records"])["Year"])
    errors = []
    sources_checked = []
    openalex = None
    arxiv_entry = None
    evidence_urls = []

    # OpenAlex often contains affiliations even when ADS leaves 'aff' blank.
    try:
        openalex = lookup_openalex(group)
        if openalex:
            sources_checked.append("OpenAlex")
            hit = openalex_affiliation(openalex)
            if hit:
                result = ("verified", "OpenAlex", hit, clean(openalex.get("id")), identifier)
                return remember_result(cache, key, result)
    except (HTTPError, URLError, TimeoutError, ValueError, json.JSONDecodeError) as exc:
        errors.append("OpenAlex: " + format_error(exc))

    # Find or discover an arXiv record with a confirmed title match.
    try:
        if identifier:
            arxiv_entry = arxiv_by_id(identifier, title)
            if not arxiv_entry:
                errors.append("arXiv: known ID did not match title")
                identifier = ""
        if not arxiv_entry:
            arxiv_entry = arxiv_by_title(title, year)
            if arxiv_entry:
                identifier = arxiv_entry["id"]
        if arxiv_entry:
            sources_checked.append("arXiv metadata")
            for affiliation in arxiv_entry["affiliations"]:
                if qualifying_affiliation(affiliation):
                    result = ("verified", "arXiv author metadata", affiliation[:320],
                              f"https://arxiv.org/abs/{identifier}", identifier)
                    return remember_result(cache, key, result)
    except (HTTPError, URLError, TimeoutError, ET.ParseError, ValueError) as exc:
        errors.append("arXiv: " + format_error(exc))

    # Prefer the arXiv PDF, but also try OA publisher PDFs if available.
    pdf_urls = ([f"https://arxiv.org/pdf/{identifier}" ] if identifier else [])
    pdf_urls += openalex_pdf_urls(openalex)
    seen = set()
    for url in pdf_urls:
        if url in seen:
            continue
        seen.add(url)
        try:
            hit, evidence_url = pdf_header_affiliation(url)
            sources_checked.append("PDF inspected")
            if hit:
                result = ("verified", "PDF affiliation", hit, evidence_url, identifier)
                return remember_result(cache, key, result)
            evidence_urls.append(url)
        except (HTTPError, URLError, TimeoutError, ValueError, RuntimeError, pymupdf.FileDataError) as exc:
            errors.append("PDF: " + format_error(exc))

    # Only a documented manual review can definitively EXCLUDE a paper.
    # Neither 'not found' nor a network failure establishes that it is non-IMAC.
    if sources_checked:
        result = ("needs_review", ", ".join(sources_checked),
                  ("No matching author affiliation established; " + "; ".join(errors))[:320],
                  evidence_urls[0] if evidence_urls else "", identifier)
    else:
        result = ("error" if errors else "needs_review", "retrieval",
                  ("; ".join(errors) or "No usable source found")[:320], "", identifier)
    return remember_result(cache, key, result)


def remember_result(cache, key, result):
    status, source, evidence, evidence_url, identifier = result
    cache[key] = {
        "cache_version": CACHE_VERSION, "status": status, "source": source,
        "evidence": evidence[:320], "evidence_url": evidence_url,
        "arxiv_id": identifier, "checked_at": datetime.now(timezone.utc).isoformat(),
    }
    return result


# Restore previously established lead-author names when NASA ADS is rate-limited.
# The older docs/imac yearly CSVs contain reliable values such as
# "Abac et al. (incl. Y. Zheng, D. Malakar)". Never infer a first author
# from the ADS bibcode or from one of the IMAC contributors.
def author_identity_keys(group):
    keys = []
    for record in group["records"]:
        if record.get("doi_key"):
            keys.append("doi:" + record["doi_key"])
        if record.get("bibcode"):
            keys.append("ads:" + record["bibcode"])
        title = decision_title_key(record["Title"])
        if title:
            keys.append("title:" + title)
    return list(dict.fromkeys(keys))


def historic_author_index():
    """Recover first-author metadata from old successful website tables.

    Read-only: never alters the live files or any publication membership.
    Old live files are read first, followed by preview files. The same
    paper is indexed by DOI, ADS bibcode and exact normalized title.
    """
    index = {}
    for directory in (LIVE_DIR, PREVIEW_DIR):
        if not directory.is_dir():
            continue
        paths = sorted(directory.glob("publications_????.csv"))
        paths += [directory / "recent_preprints.csv"]
        for path in paths:
            if not path.is_file():
                continue
            with path.open(newline="", encoding="utf-8-sig") as handle:
                for row in csv.DictReader(handle):
                    label = clean(row.get("Authors"))
                    # Ignore synthetic author labels and yearly summary rows.
                    if not label or label.startswith("IMAC contributors:"):
                        continue
                    match = re.fullmatch(
                        r"(.+?)(\s+et al\.)?\s+\(incl\.\s+[^)]+\)",
                        label, flags=re.I,
                    )
                    if not match:
                        continue
                    info = {"first_author": match.group(1).strip(),
                            "et_al": bool(match.group(2)), "source": "historic IMAC CSV"}
                    title = decision_title_key(row.get("Title"))
                    doi = doi_key(row.get("DOI URL"))
                    ads_id = bibcode(row.get("ADS URL"))
                    keys = (["title:" + title] if title else [])
                    keys += (["doi:" + doi] if doi else [])
                    keys += (["ads:" + ads_id] if ads_id else [])
                    for key in keys:
                        index.setdefault(key, info)
    return index


def load_author_cache():
    if not AUTHOR_CACHE_FILE.is_file():
        return {}
    try:
        value = json.loads(AUTHOR_CACHE_FILE.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError, json.JSONDecodeError):
        return {}


def save_author_cache(cache):
    AUTHOR_CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
    temporary = AUTHOR_CACHE_FILE.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(cache, indent=2, ensure_ascii=False, sort_keys=True)
                         + "\n", encoding="utf-8")
    os.replace(temporary, AUTHOR_CACHE_FILE)


def author_information_from_ads(docs):
    for doc in docs:
        first = doc.get("first_author") or ""
        if isinstance(first, list):
            first = first[0] if first else ""
        if not first:
            continue
        # NASA ADS first_author is conventionally "Surname, Firstname".
        surname = clean(first).split(",", 1)[0].strip()
        if not surname:
            continue
        try:
            multiple = int(doc.get("author_count") or 2) > 1
        except (TypeError, ValueError):
            multiple = True
        return {"first_author": surname, "et_al": multiple, "source": "NASA ADS"}
    return None


def first_author_from_crossref(doi):
    if not doi or doi.startswith("10.48550/arxiv."):
        return None
    url = "https://api.crossref.org/works/" + quote(doi, safe="/")
    raw = http_read(url, max_bytes=1_500_000, timeout=12,
                    headers={"Accept": "application/json"})
    obj = json.loads(raw).get("message") or {}
    authors = obj.get("author") or []
    if not isinstance(authors, list) or not authors:
        return None
    first = authors[0]
    if not isinstance(first, dict):
        return None
    name = clean(first.get("family") or first.get("name"))
    if not name:
        return None
    return {"first_author": name, "et_al": len(authors) > 1, "source": "Crossref"}


def first_author_from_openalex(group):
    obj = lookup_openalex(group)  # exact DOI lookup, never guess by title
    authors = (obj or {}).get("authorships") or []
    if not authors:
        return None
    author = authors[0].get("author") or {}
    full_name = clean(author.get("display_name"))
    if not full_name:
        return None
    # OpenAlex supplies a first-name-last-name display name, unlike ADS.
    # The final token is a reasonable short display surname; keep documented
    # multicomponent surnames from historical CSVs when they exist.
    surname = full_name.split()[-1]
    return {"first_author": surname, "et_al": len(authors) > 1,
            "source": "OpenAlex"}


def first_author_from_arxiv(group, docs):
    identifier = known_arxiv_id(group, docs)
    title = preferred_record(group["records"])["Title"]
    year = int(preferred_record(group["records"])["Year"])
    match = arxiv_by_id(identifier, title) if identifier else None
    if match is None:
        match = arxiv_by_title(title, year)
    if not match or not match.get("first_author"):
        return None
    return {"first_author": match["first_author"],
            "et_al": match.get("author_count", 2) > 1, "source": "arXiv"}


def resolve_author_information(group, docs, history, cache, budget):
    keys = author_identity_keys(group)
    info = author_information_from_ads(docs)
    if info is None:
        info = next((history[key] for key in keys if key in history), None)
    if info is None:
        info = next((cache[key] for key in keys
                     if key in cache and cache[key].get("first_author")), None)

    # Do not repeatedly contact bibliographic services for names when a
    # previously verified first author can be recovered locally.
    if info is None and budget["used"] < MAX_AUTHOR_LOOKUPS and not budget["paused"]:
        budget["used"] += 1
        dois = [r["doi_key"] for r in group["records"] if r.get("doi_key")]
        doi = next((d for d in dois if not d.startswith("10.48550/arxiv.")), "")
        if doi:
            try:
                info = first_author_from_crossref(doi)
            except HTTPError as exc:
                if exc.code in {429, 503}:
                    budget["paused"] = True
                # The author name is optional metadata: no publication fails.
            except (URLError, TimeoutError, ValueError, json.JSONDecodeError):
                pass
        if info is None and not budget["paused"] and doi:
            try:
                info = first_author_from_openalex(group)
            except HTTPError as exc:
                if exc.code in {429, 503}:
                    budget["paused"] = True
            except (URLError, TimeoutError, ValueError, json.JSONDecodeError):
                pass
        if info is None and not budget["paused"]:
            try:
                info = first_author_from_arxiv(group, docs)
            except HTTPError as exc:
                if exc.code in {429, 503}:
                    budget["paused"] = True
            except (URLError, TimeoutError, ValueError, ET.ParseError, json.JSONDecodeError):
                pass
    if info is not None:
        for key in keys:
            cache[key] = info  # persisted with the generated docs each run
    return info


def authors_label(group, docs, order, history, author_cache, author_budget):
    names = sorted(group["researchers"], key=lambda name: order.get(name, 9999))
    selected = ", ".join((name.split()[0][0] + ". " + name.split()[-1])
                         if len(name.split()) > 1 else name for name in names)
    info = resolve_author_information(group, docs, history, author_cache, author_budget)
    if info and info.get("first_author"):
        first = clean(info["first_author"])
        suffix = " et al." if info.get("et_al", True) else ""
        return f"{first}{suffix} (incl. {selected})"
    # Avoid inventing a lead author. A few papers may retain this label
    # temporarily when none of the verified metadata sources has a name.
    return f"IMAC contributors: {selected}"


def publication_row(group, ads, order, history, author_cache, author_budget):
    chosen = preferred_record(group["records"])
    docs = documents_for(group, ads)
    # Keep previous behavior: do not ADD arXiv and journal citation totals.
    counts = [int(row["Citation (ADS)"]) for row in group["records"]
              if row["Citation (ADS)"].isdigit()]
    counts += [int(doc["citation_count"]) for doc in docs
               if str(doc.get("citation_count", "")).isdigit()]
    return {
        "Title": html.escape(chosen["Title"], quote=False),
        "Authors": html.escape(authors_label(group, docs, order, history, author_cache, author_budget), quote=False),
        "Journal": html.escape(chosen["Journal"], quote=False),
        "Citation (ADS)": max(counts) if counts else "",
        "DOI URL": chosen.get("DOI URL", ""), "ADS URL": chosen.get("ADS URL", ""),
    }


def write_csv(path, rows, cols):
    tmp = path.with_suffix(".csv.tmp")
    with tmp.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=cols)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(tmp, path)


def write_summary(output, annual, statuses):
    """Summarize exactly the verified published papers in the yearly CSVs.

    Keep Shun's requested wording even while affiliation checks are ongoing;
    show PRELIMINARY clearly in a separate explanatory line.
    """
    current = datetime.now(timezone.utc).year
    papers = [
        row
        for year, rows in annual.items()
        if START_YEAR <= int(year) <= current
        for row in rows
    ]
    citation_counts = [
        int(str(row["Citation (ADS)"]))
        for row in papers
        if str(row["Citation (ADS)"]).isdigit()
    ]
    n = len(papers)
    total = sum(citation_counts)
    unresolved = sum(statuses[s] for s in ("pending", "needs_review", "error"))

    # The exact sentence requested by Shun; dynamically populated.
    sentence = (
        f"IMAC published a total of {n:,} articles cited a total of "
        f"{total:,} times (according to NASA ADS)"
    )

    detail = (
        f"2019–{current}; verified institutional affiliations. "
        f"ADS citation counts available for {len(citation_counts)}/{n} articles. "
        + (f"PRELIMINARY: {unresolved} publications remain unresolved. "
           if unresolved else "")
        + "Citation counts are cumulative to date."
        + (" NOTE: ADS rate limit reached; citation counts were retained from "
           "saved publication CSVs and may be out of date." if ADS_RATE_LIMITED else "")
    )

    # CSV and JSON use the same exact summary wording as the HTML display.
    with (output / "summary_statistics.csv").open(
        "w", newline="", encoding="utf-8"
    ) as handle:
        writer = csv.writer(handle)
        writer.writerow(["IMAC Publication Summary"])
        writer.writerow([sentence])

    (output / "summary.json").write_text(
        json.dumps({
            "start_year": START_YEAR,
            "end_year": current,
            "published_articles": n,
            "ads_citations": total,
            "papers_with_ads_data": len(citation_counts),
            "unresolved_affiliations": unresolved,
            "preliminary": bool(unresolved),
            "verification_statuses": dict(statuses),
            "summary": sentence,
            "note": detail,
        }, indent=2),
        encoding="utf-8",
    )

    # Only the two dynamic numbers are enlarged; the original sentence
    # remains 20 px, with a small preliminary / methodology note below.
    styled_sentence = (
        "IMAC published a total of "
        f'<strong class="stat-count">{n:,}</strong> '
        "articles cited a total of "
        f'<strong class="stat-count">{total:,}</strong> '
        "times (according to NASA ADS)"
    )
    (output / "summary.html").write_text(
        "<!doctype html><html lang='en'><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        "<style>"
        "body{font-family:Arial,sans-serif;color:#003c4a;"
        "margin:10px;text-align:center}"
        "p{font-size:20px;font-weight:600;line-height:1.6;margin:12px 0 8px}"
        ".stat-count{font-size:36px;font-weight:800;display:inline-block;"
        "line-height:1.15;white-space:nowrap}"
        "small{font-size:12px;color:#555;line-height:1.5;display:block}"
        "@media(max-width:600px){.stat-count{font-size:28px}}"
        "</style></head><body>"
        f"<p>{styled_sentence}</p>"
        f"<small>{html.escape(detail)}</small>"
        "</body></html>",
        encoding="utf-8",
    )
    print(sentence)
    print(detail)
    return n, unresolved


def main():
    token = os.getenv("ADS_API_TOKEN")
    if not token:
        raise RuntimeError("ADS_API_TOKEN secret is missing")
    if MODE not in {"preview", "live"}:
        raise ValueError("IMAC_OUTPUT_MODE must be preview or live")
    if MAX_CHECKS < 0:
        raise ValueError("IMAC_MAX_NEW_CHECKS cannot be negative")

    researchers, records = load_records()
    groups = collapse(records)
    year_now = datetime.now(timezone.utc).year
    groups = [group for group in groups if START_YEAR <= int(preferred_record(group["records"])["Year"]) <= year_now]
    print(f"Unique 2019–{year_now} works: {len(groups)}")
    selected_records = [row for group in groups for row in group["records"]]
    global HISTORIC_AUDIT
    HISTORIC_AUDIT = load_historic_audit()
    ads = fetch_ads(selected_records, token)
    # Without ADS or any previous audit there is no reliable affiliation
    # baseline. Refuse to overwrite verified tables with a partial listing.
    if ADS_RATE_LIMITED and not HISTORIC_AUDIT:
        raise RuntimeError(
            "NASA ADS rate-limited and no previous verified audit exists. "
            "Existing preview files were not overwritten. Try the next daily run."
        )
    cache, decisions = load_cache(), load_decisions()
    author_history, author_cache = historic_author_index(), load_author_cache()
    author_budget = {"used": 0, "paused": False}
    print(f"Previously known first-author labels: {len(author_history)} keys")
    order = {person["name"]: i for i, person in enumerate(researchers)}
    statuses, budget = Counter(), {"used": 0}
    annual, preprints, audit = defaultdict(list), [], []

    # Priority only determines which work is checked first, not CSV order.
    groups.sort(key=lambda group: (is_priority(group), int(preferred_record(group["records"])["Year"])), reverse=True)
    for group in groups:
        chosen = preferred_record(group["records"])
        status, source, evidence, evidence_url, identifier = verify(group, ads, cache, decisions, budget)
        statuses[status] += 1
        audit.append({
            "Year": chosen["Year"], "Title": chosen["Title"], "Status": status,
            "Source": source, "Evidence": evidence, "Evidence URL": evidence_url,
            "arXiv": identifier, "DOI URL": chosen.get("DOI URL", ""),
            "ADS URL": chosen.get("ADS URL", ""),
        })
        if is_priority(group):
            print(f"PRIORITY PAPER arXiv:{PRIORITY_ARXIV}: {status} | {source} | {evidence[:160]}")
        if status != "verified":
            continue
        row = publication_row(group, ads, order, author_history, author_cache, author_budget)
        if chosen["preprint"]:
            if int(chosen["Year"]) >= year_now - 1:
                preprints.append(row)
        elif chosen["Journal"]:
            annual[chosen["Year"]].append(row)

    log_manual_coverage(decisions)

    output = PREVIEW_DIR if MODE == "preview" else LIVE_DIR
    verified_count = sum(len(items) for items in annual.values())
    unresolved = sum(statuses[s] for s in ("pending", "needs_review", "error"))
    # No partial live updates; preview remains safe for additional verification.
    if MODE == "live" and (verified_count == 0 or unresolved):
        raise RuntimeError("Live update blocked: unresolved affiliation checks remain")
    output.mkdir(parents=True, exist_ok=True)
    save_cache(cache)
    save_author_cache(author_cache)
    print(f"New author lookups: {author_budget['used']}/{MAX_AUTHOR_LOOKUPS}")
    years = {str(y) for y in range(START_YEAR, year_now + 1)} | set(annual)
    for path in LIVE_DIR.glob("publications_*.csv"):
        match = re.fullmatch(r"publications_(\d{4})\.csv", path.name)
        if match and START_YEAR <= int(match.group(1)) <= year_now:
            years.add(match.group(1))
    for year in sorted(years, reverse=True):
        rows = sorted(annual.get(year, []), key=lambda row: row["Title"].casefold())
        write_csv(output / f"publications_{year}.csv", rows, CSV_COLUMNS)
        print(f"{year}: {len(rows)} verified published papers")
    write_csv(output / "recent_preprints.csv",
              sorted(preprints, key=lambda row: row["Title"].casefold()), CSV_COLUMNS)
    write_summary(output, annual, statuses)
    if ADS_RATE_LIMITED:
        print("WARNING: NASA ADS rate-limited. New affiliations may remain "
              "unresolved and citations may reflect the last saved CSV values.")
    audit.sort(key=lambda row: (-int(row["Year"]), row["Title"].casefold()))
    write_csv(output / "affiliation_audit.csv", audit, AUDIT_COLUMNS)
    write_csv(output / "affiliation_review.csv",
              [row for row in audit if row["Status"] not in {"verified", "excluded"}], AUDIT_COLUMNS)
    print("Affiliation statuses:", dict(statuses))
    print(f"New fallback checks: {budget['used']}/{MAX_CHECKS}; mode: {MODE}; directory: {output}")


if __name__ == "__main__":
    main()
