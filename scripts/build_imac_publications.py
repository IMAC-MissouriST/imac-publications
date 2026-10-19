"""Build IMAC publications with affiliation verification and a preview report.

Inputs: researchers.json and docs/publications/<ORCID>.csv.
Verification: NASA ADS -> arXiv author metadata -> open-access PDF.
Output: docs/imac_affiliation_preview/ (default), or docs/imac/ when
IMAC_OUTPUT_MODE=live. Individual researcher CSVs are never modified.
"""

import csv
import html
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
LIVE_OUTPUT = ROOT / "docs" / "imac"
PREVIEW_OUTPUT = ROOT / "docs" / "imac_affiliation_preview"
CACHE_FILE = PREVIEW_OUTPUT / "affiliation_cache.json"
CONFIG = ROOT / "researchers.json"
ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"
ARXIV_API = "https://export.arxiv.org/api/query"
START_YEAR = 2019
MODE = os.environ.get("IMAC_OUTPUT_MODE", "preview").strip().lower()
MAX_NEW_CHECKS = int(os.environ.get("IMAC_MAX_NEW_CHECKS", "30"))
MAX_PDF_BYTES = 16 * 1024 * 1024
PRIORITY_ARXIV = "2507.16707"  # Initial PDF test case; not an inclusion override.
USER_AGENT = "IMAC-Publications/1.2 (automated scholarly metadata checker)"
FIELDS = ["Title", "Authors", "Journal", "Citation (ADS)", "DOI URL", "ADS URL"]
AUDIT_FIELDS = ["Year", "Title", "Status", "Source", "Evidence", "arXiv", "DOI URL", "ADS URL"]
ATOM = "{http://www.w3.org/2005/Atom}"
ARXIV_NS = "{http://arxiv.org/schemas/atom}"
LAST_ARXIV_REQUEST = 0.0

AFFILIATION_PATTERNS = [
    re.compile(r"\bMissouri\s+University\s+of\s+Science\s*(?:and|&)\s*Technology\b", re.I),
    re.compile(r"\bMissouri\s+S\s*(?:&|and)\s*T\b", re.I),
    re.compile(r"\bInstitute\s+for\s+Multi[\s-]*messenger\s+Astrophysics\s*(?:and|&)\s*Cosmology\b", re.I),
]
ARXIV_ID_PATTERN = re.compile(
    r"(?i)(?:arxiv(?:\.org/(?:abs|pdf)/|[:./\s])|10\.48550/arxiv\.)"
    r"(\d{4}\.\d{4,5})(?:v\d+)?"
)
ARXIV_BIB_PATTERN = re.compile(r"\d{4}arXiv(\d{4})(\d{4,5})", re.I)


def plain(value):
    return html.unescape(html.unescape(str(value or ""))).strip()


def title_key(value):
    value = unicodedata.normalize("NFKD", plain(value)).casefold()
    value = value.replace(r"\alpha", "alpha").replace("α", "alpha")
    return re.sub(r"[^a-z0-9]", "", value)


def doi_key(value):
    value = re.sub(r"^https?://(?:dx\.)?doi\.org/", "", plain(value), flags=re.I)
    return unquote(re.sub(r"^doi:\s*", "", value, flags=re.I)).casefold()


def bibcode_from_url(value):
    match = re.search(r"/abs/([^/?#]+)", plain(value))
    return unquote(match.group(1)) if match else ""


def is_preprint(row):
    return ("arxiv" in row["Journal"].casefold()
            or row["doi_key"].startswith("10.48550/arxiv.")
            or row["Title"].casefold().startswith("arxiv:"))


def normalize_affiliation(value):
    value = plain(value)
    value = re.sub(r"(?<=\w)-\s*\n\s*(?=\w)", "-", value)
    return re.sub(r"\s+", " ", value)


def affiliation_match(text):
    return any(pattern.search(normalize_affiliation(text)) for pattern in AFFILIATION_PATTERNS)


def read_records():
    researchers = json.loads(CONFIG.read_text(encoding="utf-8"))["researchers"]
    if not researchers:
        raise RuntimeError("No researchers in researchers.json")
    records = []
    for person in researchers:
        file = SOURCE / f'{person["orcid"]}.csv'
        if not file.is_file():
            raise FileNotFoundError(f"Missing researcher CSV: {file}")
        with file.open(newline="", encoding="utf-8-sig") as stream:
            reader = csv.DictReader(stream)
            columns = set(reader.fieldnames or [])
            required = {"Year", "Title", "Journal", "DOI URL", "ADS URL"}
            if not required.issubset(columns) or not ({"Citation (ADS)", "Citations"} & columns):
                raise ValueError(f"Unexpected columns in {file}")
            for row in reader:
                year, title = plain(row.get("Year")), plain(row.get("Title"))
                if len(year) != 4 or not year.isdigit() or not title:
                    continue
                citation = row.get("Citation (ADS)") or row.get("Citations") or ""
                row.update({
                    "Year": year, "Title": title, "Journal": plain(row.get("Journal")),
                    "Citation (ADS)": str(citation).strip(), "researcher": person["name"],
                    "doi_key": doi_key(row.get("DOI URL")),
                    "bibcode": bibcode_from_url(row.get("ADS URL")), "title_key": title_key(title),
                })
                row["preprint"] = is_preprint(row)
                records.append(row)
    if not records:
        raise RuntimeError("No publication records found")
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
        other_key = other["title_key"]
        if abs(int(row["Year"]) - int(other["Year"])) > 2:
            continue
        if key == other_key:
            return True
        if (len(other_key) >= 35
                and re.findall(r"\d+", key) == re.findall(r"\d+", other_key)
                and SequenceMatcher(None, key, other_key).ratio() >= 0.985):
            return True
    return False


def collapse(records):
    clusters = []
    for row in records:
        cluster = next((c for c in clusters if same_paper(row, c)), None)
        if cluster is None:
            cluster = {"records": [], "researchers": set(), "dois": set(), "bibcodes": set()}
            clusters.append(cluster)
        cluster["records"].append(row)
        cluster["researchers"].add(row["researcher"])
        if row["doi_key"]:
            cluster["dois"].add(row["doi_key"])
        if row["bibcode"]:
            cluster["bibcodes"].add(row["bibcode"])
    return clusters


def best_record(records):
    def rank(row):
        citation = row["Citation (ADS)"]
        return (not row["preprint"], bool(row["Journal"]), bool(row["doi_key"]),
                bool(row["bibcode"]), int(citation) if citation.isdigit() else -1)
    return max(records, key=rank)


def is_priority_paper(cluster):
    for row in cluster["records"]:
        identifiers = " ".join(str(row.get(key, "")) for key in ("DOI URL", "ADS URL", "Title"))
        title = row["title_key"]
        if (PRIORITY_ARXIV in identifiers or
                ("simulatingrealistic" in title and "radiativetransfer" in title and "lyman" in title)):
            return True
    return False


def fetch_ads(records, token):
    lookups = sorted({("bibcode", r["bibcode"]) for r in records if r["bibcode"]})
    lookups += sorted({("doi", r["doi_key"]) for r in records if r["doi_key"]})
    by_bibcode, by_doi = {}, {}
    for start in range(0, len(lookups), 15):
        clauses = []
        for field, value in lookups[start:start + 15]:
            escaped = value.replace("\\", "\\\\").replace('"', '\\"')
            clauses.append(f'{field}:"{escaped}"')
        url = ADS_API + "?" + urlencode({
            "q": " OR ".join(clauses),
            "fl": "bibcode,doi,identifier,first_author,author_count,aff,citation_count",
            "rows": 200,
        })
        request = Request(url, headers={"Authorization": f"Bearer {token}",
                                        "Accept": "application/json", "User-Agent": USER_AGENT})
        try:
            with urlopen(request, timeout=75) as reply:
                data = json.load(reply)
        except (HTTPError, URLError, TimeoutError) as exc:
            raise RuntimeError(f"ADS metadata request failed: {type(exc).__name__}") from exc
        response = data.get("response", {})
        docs = response.get("docs")
        if not isinstance(docs, list) or response.get("numFound", 0) > len(docs):
            raise RuntimeError("Incomplete ADS metadata response; update stopped")
        for document in docs:
            bibcode = document.get("bibcode")
            if bibcode:
                by_bibcode[bibcode] = document
            dois = document.get("doi") or []
            if isinstance(dois, str):
                dois = [dois]
            for doi in dois:
                by_doi[doi_key(doi)] = document
    return by_bibcode, by_doi


def documents_for(cluster, metadata):
    bibcodes, dois = metadata
    documents, seen = [], set()
    for row in cluster["records"]:
        for document in (bibcodes.get(row["bibcode"]), dois.get(row["doi_key"])):
            if document:
                key = document.get("bibcode") or id(document)
                if key not in seen:
                    seen.add(key)
                    documents.append(document)
    return documents


def ads_affiliation(documents):
    seen_affiliation = False
    for document in documents:
        affiliations = document.get("aff") or []
        if isinstance(affiliations, str):
            affiliations = [affiliations]
        for value in affiliations:
            value = normalize_affiliation(value)
            if value.casefold() in {"", "-", "n/a", "none", "unknown", "not available"}:
                continue
            seen_affiliation = True
            if affiliation_match(value):
                return True, value[:350], "ADS"
    detail = "ADS affiliations did not match IMAC" if seen_affiliation else "ADS affiliations unavailable"
    return False, detail, "ADS"


def arxiv_id_for(cluster, documents):
    # Priority affects CHECK ORDER only; it does not automatically qualify the paper.
    if is_priority_paper(cluster):
        return PRIORITY_ARXIV
    pieces = []
    for row in cluster["records"]:
        pieces += [row.get("DOI URL", ""), row.get("ADS URL", ""),
                   row.get("Title", ""), row.get("Journal", "")]
    for document in documents:
        ids = document.get("identifier") or []
        if isinstance(ids, str):
            ids = [ids]
        pieces += ids + [document.get("bibcode", "")]
    for piece in pieces:
        match = ARXIV_ID_PATTERN.search(str(piece))
        if match:
            return match.group(1)
        match = ARXIV_BIB_PATTERN.search(str(piece))
        if match:
            return f"{match.group(1)}.{match.group(2)}"
    return ""


def wait_for_arxiv():
    global LAST_ARXIV_REQUEST
    delta = time.monotonic() - LAST_ARXIV_REQUEST
    if LAST_ARXIV_REQUEST and delta < 3.1:
        time.sleep(3.1 - delta)
    LAST_ARXIV_REQUEST = time.monotonic()


def arxiv_author_affiliation(identifier):
    wait_for_arxiv()
    url = ARXIV_API + "?" + urlencode({"id_list": identifier, "max_results": 1})
    with urlopen(Request(url, headers={"User-Agent": USER_AGENT}), timeout=35) as reply:
        root = ET.fromstring(reply.read(512_000))
    for entry in root.findall(ATOM + "entry"):
        for author in entry.findall(ATOM + "author"):
            for affiliation in author.findall(ARXIV_NS + "affiliation"):
                if affiliation.text and affiliation_match(affiliation.text):
                    return normalize_affiliation(affiliation.text)[:350]
    return ""


def openalex_pdf_url(cluster):
    doi = best_record(cluster["records"])["doi_key"]
    if not doi or doi.startswith("10.48550/arxiv."):
        return ""
    url = "https://api.openalex.org/works/https://doi.org/" + quote(doi, safe="/")
    with urlopen(Request(url, headers={"User-Agent": USER_AGENT,
                                       "Accept": "application/json"}), timeout=25) as reply:
        obj = json.load(reply)
    locations = [obj.get("best_oa_location") or {}] + (obj.get("locations") or [])
    for location in locations:
        pdf_url = location.get("pdf_url") or ""
        parts = urlsplit(pdf_url)
        if parts.scheme == "https" and parts.hostname and parts.hostname != "localhost":
            return pdf_url
    return ""


def pdf_affiliation(pdf_url):
    parts = urlsplit(pdf_url)
    if parts.scheme != "https" or not parts.hostname or parts.hostname in {
        "localhost", "127.0.0.1", "169.254.169.254"
    }:
        return "", "Invalid or unsafe PDF URL"
    if parts.hostname.endswith("arxiv.org"):
        wait_for_arxiv()
    request = Request(pdf_url, headers={"User-Agent": USER_AGENT,
                                        "Accept": "application/pdf"})
    with urlopen(request, timeout=50) as reply:
        raw = reply.read(MAX_PDF_BYTES + 1)
    if len(raw) > MAX_PDF_BYTES:
        return "", "PDF exceeds download limit"
    if not raw.lstrip().startswith(b"%PDF"):
        return "", "Source did not return a PDF"
    with pymupdf.open(stream=raw, filetype="pdf") as document:
        for page_num in range(min(len(document), 2)):
            text = document[page_num].get_text("text", sort=True)
            if page_num == 0:
                # Inspect byline and author-affiliation header only.
                stop = re.search(r"\b(?:ABSTRACT|INTRODUCTION)\b", text, flags=re.I)
                candidate = text[:stop.start()] if stop else text[:8500]
            else:
                # On page two, require an explicit affiliation heading.
                if not re.search(r"(?i)affiliations?\s*(?:of\s+authors)?", text[:700]):
                    continue
                candidate = text[:4500]
            if affiliation_match(candidate):
                normalized = normalize_affiliation(candidate)
                hit = next((p.search(normalized) for p in AFFILIATION_PATTERNS
                            if p.search(normalized)), None)
                evidence = normalized[max(0, hit.start() - 65):hit.end() + 100] if hit else normalized[:350]
                return evidence[:350], f"PDF page {page_num + 1}"
    return "", "No IMAC affiliation in inspected PDF header"


def cache_key(cluster, identifier):
    row = best_record(cluster["records"])
    if row["doi_key"]:
        return "doi:" + row["doi_key"]
    if identifier:
        return "arxiv:" + identifier
    if row["bibcode"]:
        return "ads:" + row["bibcode"]
    return "title:" + row["title_key"]


def load_cache():
    if CACHE_FILE.exists():
        value = json.loads(CACHE_FILE.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    return {}


def save_cache(cache):
    CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
    temporary = CACHE_FILE.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(cache, indent=2, sort_keys=True), encoding="utf-8")
    os.replace(temporary, CACHE_FILE)


def verify_affiliation(cluster, metadata, cache, checks):
    documents = documents_for(cluster, metadata)
    found, evidence, source = ads_affiliation(documents)
    if found:
        return "verified", source, evidence, ""
    identifier = arxiv_id_for(cluster, documents)
    key = cache_key(cluster, identifier)
    old = cache.get(key)
    if old:
        try:
            age = (datetime.now(timezone.utc) -
                   datetime.fromisoformat(old["checked_at"])).days
        except (KeyError, TypeError, ValueError):
            age = 999
        threshold = 3 if old.get("status") == "error" else 30
        if old.get("status") == "verified" or age < threshold:
            return (old.get("status", "unverified"),
                    old.get("source", "cache"), old.get("evidence", ""), identifier)
    if checks["used"] >= MAX_NEW_CHECKS:
        return "pending", "budget", "Pending affiliation check on a later run", identifier
    checks["used"] += 1
    status, method, detail = "unverified", "none", "No verified affiliation found"
    errors = []
    if identifier:
        try:
            hit = arxiv_author_affiliation(identifier)
            if hit:
                status, method, detail = "verified", "arXiv author metadata", hit
        except (HTTPError, URLError, TimeoutError, ET.ParseError, ValueError) as exc:
            errors.append("arXiv metadata: " + type(exc).__name__)
    if status != "verified":
        pdf_url = "https://arxiv.org/pdf/" + identifier if identifier else ""
        if not pdf_url:
            try:
                pdf_url = openalex_pdf_url(cluster)
            except (HTTPError, URLError, TimeoutError, ValueError) as exc:
                errors.append("OpenAlex: " + type(exc).__name__)
        if pdf_url:
            try:
                hit, detail = pdf_affiliation(pdf_url)
                if hit:
                    status, method, detail = "verified", "PDF header", hit
                else:
                    method = "PDF checked"
            except (HTTPError, URLError, TimeoutError, RuntimeError, ValueError) as exc:
                errors.append("PDF: " + type(exc).__name__)
    if status != "verified" and errors:
        status = "error"
        detail = "; ".join(errors)[:350]
    cache[key] = {
        "status": status, "source": method, "evidence": detail[:350],
        "checked_at": datetime.now(timezone.utc).isoformat(), "arxiv_id": identifier,
    }
    return status, method, detail, identifier


def author_label(cluster, documents, order):
    names = sorted(cluster["researchers"], key=lambda name: order.get(name, 9999))
    included = ", ".join((name.split()[0][0] + ". " + name.split()[-1])
                         if len(name.split()) > 1 else name for name in names)
    for document in documents:
        first = document.get("first_author") or ""
        if isinstance(first, list):
            first = first[0] if first else ""
        if first:
            surname = plain(first).split(",")[0]
            try:
                multiple = int(document.get("author_count") or 2) > 1
            except (TypeError, ValueError):
                multiple = True
            return f"{surname}{' et al.' if multiple else ''} (incl. {included})"
    return f"IMAC contributors: {included}"


def output_row(cluster, metadata, order):
    chosen = best_record(cluster["records"])
    documents = documents_for(cluster, metadata)
    # As in the existing workflow, use maximum rather than summing
    # journal and arXiv counts for the same deduplicated work.
    counts = [int(r["Citation (ADS)"]) for r in cluster["records"]
              if r["Citation (ADS)"].isdigit()]
    counts += [int(d["citation_count"]) for d in documents
               if str(d.get("citation_count", "")).isdigit()]
    return {
        "Title": html.escape(plain(chosen["Title"]), quote=False),
        "Authors": html.escape(author_label(cluster, documents, order), quote=False),
        "Journal": html.escape(plain(chosen["Journal"]), quote=False),
        "Citation (ADS)": max(counts) if counts else "",
        "DOI URL": chosen["DOI URL"], "ADS URL": chosen["ADS URL"],
    }


def write_csv(path, rows, fieldnames):
    temporary = path.with_suffix(".csv.tmp")
    with temporary.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(temporary, path)


def write_summary(output, annual, statuses):
    now = datetime.now(timezone.utc).year
    papers = [r for year, rows in annual.items()
              if START_YEAR <= int(year) <= now for r in rows]
    citations = [int(str(r["Citation (ADS)"])) for r in papers
                 if str(r["Citation (ADS)"]).isdigit()]
    count, total = len(papers), sum(citations)
    noun = "article" if count == 1 else "articles"
    statement = (f"IMAC published a total of {count:,} {noun}, "
                 f"cited a total of {total:,} times (according to NASA ADS).")
    unresolved = sum(statuses[s] for s in ("pending", "unverified", "error"))
    note = (f"2019–{now}; verified affiliations; ADS citation counts available "
            f"for {len(citations)}/{count} articles. "
            + (f"PRELIMINARY: {unresolved} publications remain unresolved. "
               if unresolved else "")
            + "Citation counts are cumulative, not citations received in these years.")
    with (output / "summary_statistics.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(["IMAC Publication Summary"])
        writer.writerow([statement])
    (output / "summary.json").write_text(json.dumps({
        "start_year": START_YEAR, "end_year": now, "published_articles": count,
        "ads_citations": total, "papers_with_ads_data": len(citations),
        "unresolved_affiliations": unresolved, "preliminary": bool(unresolved),
        "summary": statement, "note": note,
    }, indent=2), encoding="utf-8")
    (output / "summary.html").write_text(
        "<!doctype html><html lang='en'><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        "<style>body{font-family:Arial,sans-serif;color:#003c4a;margin:10px;"
        "text-align:center}p{font-size:20px;font-weight:600;line-height:1.5}"
        "small{font-size:12px;color:#555}</style></head><body>"
        f"<p>{html.escape(statement)}</p><small>{html.escape(note)}</small>"
        "</body></html>", encoding="utf-8")
    print(statement)
    print(note)
    return count


def sort_audit_by_year(audit):
    """Report order is separate from verification priority.

    Newest year first; alphabetically by title within each year.
    """
    return sorted(audit, key=lambda row: (-int(row["Year"]), plain(row["Title"]).casefold()))


def main():
    token = os.environ.get("ADS_API_TOKEN")
    if not token:
        raise RuntimeError("Missing ADS_API_TOKEN secret")
    if MODE not in {"preview", "live"}:
        raise ValueError("IMAC_OUTPUT_MODE must be 'preview' or 'live'")
    researchers, records = read_records()
    clusters = collapse(records)
    now = datetime.now(timezone.utc).year
    total_clusters = len(clusters)
    clusters = [c for c in clusters if START_YEAR <= int(best_record(c["records"])["Year"]) <= now]
    recent_records = [r for c in clusters for r in c["records"]]
    print(f"Unique works overall: {total_clusters}; from {START_YEAR}–{now}: {len(clusters)}")
    metadata = fetch_ads(recent_records, token)
    order = {person["name"]: i for i, person in enumerate(researchers)}
    cache, checks = load_cache(), {"used": 0}
    annual, preprints, audit, statuses = defaultdict(list), [], [], Counter()

    # CHECK priority: initial test paper first, then newest to oldest.
    # This does NOT determine the display order in affiliation_audit.csv.
    clusters.sort(key=lambda c: (int(is_priority_paper(c)),
                                  int(best_record(c["records"])["Year"])), reverse=True)
    print(f"Priority paper present: {any(is_priority_paper(c) for c in clusters)}")
    for cluster in clusters:
        chosen = best_record(cluster["records"])
        if is_priority_paper(cluster):
            # Retry test paper if old cache recorded a failure, keeping positive matches.
            identifier = arxiv_id_for(cluster, documents_for(cluster, metadata))
            key = cache_key(cluster, identifier)
            if key in cache and cache[key].get("status") != "verified":
                del cache[key]
        status, source, evidence, identifier = verify_affiliation(cluster, metadata, cache, checks)
        statuses[status] += 1
        if is_priority_paper(cluster):
            print("=" * 55)
            print("PRIORITY PAPER TEST RESULT: arXiv:" + PRIORITY_ARXIV)
            print(f"Status: {status}; Source: {source}; Evidence: {evidence}; arXiv: {identifier}")
            print("=" * 55)
        audit.append({
            "Year": chosen["Year"], "Title": chosen["Title"], "Status": status,
            "Source": source, "Evidence": evidence, "arXiv": identifier,
            "DOI URL": chosen["DOI URL"], "ADS URL": chosen["ADS URL"],
        })
        if status != "verified":
            continue
        row = output_row(cluster, metadata, order)
        if chosen["preprint"]:
            if int(chosen["Year"]) >= now - 1:
                preprints.append(row)
        elif chosen["Journal"]:
            annual[chosen["Year"]].append(row)

    output = PREVIEW_OUTPUT if MODE == "preview" else LIVE_OUTPUT
    count = sum(len(rows) for rows in annual.values())
    # Safety: refuse incomplete live updates BEFORE writing any live files.
    if MODE == "live" and (count == 0 or sum(statuses[s] for s in ("pending", "unverified", "error"))):
        raise RuntimeError("Live update blocked: paper affiliation verification is incomplete")
    output.mkdir(parents=True, exist_ok=True)
    save_cache(cache)
    years = {str(year) for year in range(START_YEAR, now + 1)} | set(annual)
    for path in LIVE_OUTPUT.glob("publications_*.csv"):
        match = re.fullmatch(r"publications_(\d{4})\.csv", path.name)
        if match and START_YEAR <= int(match.group(1)) <= now:
            years.add(match.group(1))
    for year in sorted(years, reverse=True):
        rows = sorted(annual.get(year, []), key=lambda r: r["Title"].casefold())
        write_csv(output / f"publications_{year}.csv", rows, FIELDS)
        print(f"{year}: {len(rows)} verified published works")
    write_csv(output / "recent_preprints.csv",
              sorted(preprints, key=lambda r: r["Title"].casefold()), FIELDS)
    write_summary(output, annual, statuses)

    # DISPLAY priority: newest year first, alphabetical titles within each year.
    # Your 2025 paper is still CHECKED first but appears among 2025 records.
    audit = sort_audit_by_year(audit)
    write_csv(output / "affiliation_audit.csv", audit, AUDIT_FIELDS)
    write_csv(output / "affiliation_review.csv",
              [r for r in audit if r["Status"] != "verified"], AUDIT_FIELDS)
    print("Verification statuses:", dict(statuses))
    print(f"New affiliation checks: {checks['used']} / {MAX_NEW_CHECKS}")
    print(f"Output mode: {MODE}; files in {output}")


if __name__ == "__main__":
    main()
