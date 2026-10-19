"""Incremental ORCID + NASA ADS updater for IMAC.

Six-column CSV interface unchanged. ADS citations are cached between GitHub
Actions runs. HTTP 429 switches this run to saved citations, instead of
terminating the workflow or falsely reporting unavailable counts as zero.

The ADS cache intentionally lives under docs/publications so GitHub Actions
commits it as part of docs/. It contains only public bibliographic metadata.
"""
import csv
import html
import json
import os
import re
import time
from datetime import datetime, timezone, timedelta
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote, unquote, urlencode
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent.parent
CONFIG_FILE = ROOT / "researchers.json"
OUTPUT_DIR = ROOT / "docs" / "publications"
CACHE_FILE = OUTPUT_DIR / "ads_metadata_cache.json"
ADS_API_URL = "https://api.adsabs.harvard.edu/v1/search/query"
COLUMNS = ["Year", "Title", "Journal", "Citation (ADS)", "DOI URL", "ADS URL"]
USER_AGENT = "IMAC-Publications-Updater/3.0 (institutional bibliography)"
ADS_REFRESH_DAYS = max(1, int(os.getenv("ADS_REFRESH_DAYS", "14")))
ADS_MAX_REQUESTS = max(0, int(os.getenv("ADS_MAX_REQUESTS", "40")))
ADS_PAUSE_SECONDS = float(os.getenv("ADS_PAUSE_SECONDS", "0.4"))

ADS_CACHE = {}
ADS_LIMITED = False
ADS_REQUESTS = 0
LAST_ADS = 0.0


def clean_text(value):
    text = html.unescape(str(value or ""))
    superscripts = str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹")
    text = re.sub(r"<sup\b[^>]*>(.*?)</sup>",
                  lambda m: m.group(1).translate(superscripts), text, flags=re.I)
    text = re.sub(r"</?(?:i|em|b|strong|span|sub)\b[^>]*>", "", text, flags=re.I)
    return " ".join(text.split())


def title_key(text):
    return re.sub(r"[^a-z0-9]+", "", clean_text(text).casefold())


def normalize_doi(doi):
    doi = str(doi or "").strip()
    doi = re.sub(r"^https?://(?:dx\.)?doi\.org/", "", doi, flags=re.I)
    doi = re.sub(r"^doi:\s*", "", doi, flags=re.I)
    return unquote(doi).strip()


def fetch_orcid_works(orcid):
    url = f"https://pub.orcid.org/v3.0/{orcid}/works"
    request = Request(url, headers={
        "Accept": "application/vnd.orcid+json", "User-Agent": USER_AGENT})
    with urlopen(request, timeout=60) as response:
        data = json.load(response)
    if not isinstance(data, dict) or not isinstance(data.get("group"), list):
        raise ValueError(f"Unexpected ORCID response for {orcid}")
    return data["group"]


def get_identifier(group, id_type):
    sources = [group] + (group.get("work-summary") or [])
    for source in sources:
        for item in (source.get("external-ids") or {}).get("external-id") or []:
            if (item.get("external-id-type") or "").lower() == id_type.lower():
                return ((item.get("external-id-normalized") or {}).get("value")
                        or item.get("external-id-value") or "")
    return ""


def read_existing(orcid):
    path = OUTPUT_DIR / f"{orcid}.csv"
    if not path.exists():
        return []
    with path.open(newline="", encoding="utf-8-sig") as stream:
        reader = csv.DictReader(stream)
        if not set(COLUMNS).issubset(set(reader.fieldnames or [])):
            raise RuntimeError(f"Existing CSV has unexpected columns: {path}")
        return list(reader)


def previous_index(records):
    by_doi, by_title = {}, {}
    for row in records:
        doi = normalize_doi(row.get("DOI URL")).casefold()
        if doi:
            by_doi[doi] = row
        key = (str(row.get("Year", "")), title_key(row.get("Title")))
        if key[1]:
            by_title[key] = row
    return by_doi, by_title


def cache_key(field, value):
    return f"{field}:{str(value).strip().casefold()}"


def load_ads_cache():
    global ADS_CACHE
    if not CACHE_FILE.exists():
        ADS_CACHE = {}
        return
    payload = json.loads(CACHE_FILE.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or payload.get("version") != 1:
        raise ValueError("Unsupported ADS metadata cache version")
    records = payload.get("records")
    if not isinstance(records, dict):
        raise ValueError("Invalid ADS cache records")
    ADS_CACHE = records


def save_ads_cache():
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = {"version": 1, "records": ADS_CACHE}
    temp = CACHE_FILE.with_name(CACHE_FILE.name + ".tmp")
    temp.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8")
    os.replace(temp, CACHE_FILE)


def keys_for(doi, bibcode):
    items = []
    if bibcode:
        items.append(cache_key("bibcode", bibcode))
    if doi:
        items.append(cache_key("doi", normalize_doi(doi)))
    return items


def cached_metadata(doi, bibcode):
    for key in keys_for(doi, bibcode):
        item = ADS_CACHE.get(key)
        if isinstance(item, dict):
            return item
    return None


def seed_cache(doi, bibcode, row):
    """Use previously published CSV data, never overwrite a fresher cache."""
    if not row:
        return
    old_url = row.get("ADS URL") or ""
    if not bibcode and "/abs/" in old_url:
        bibcode = unquote(old_url.split("/abs/", 1)[1].split("/", 1)[0])
    keys = keys_for(doi, bibcode)
    if not keys or any(key in ADS_CACHE for key in keys):
        return
    count = row.get("Citation (ADS)", "")
    metadata = {"bibcode": bibcode, "citation_count": count,
                "checked_at": datetime.now(timezone.utc).isoformat(),
                "source": "previous published CSV"}
    for key in keys:
        ADS_CACHE[key] = metadata


def cache_fresh(item):
    try:
        stamp = datetime.fromisoformat(item["checked_at"])
        if stamp.tzinfo is None:
            stamp = stamp.replace(tzinfo=timezone.utc)
        return datetime.now(timezone.utc) - stamp < timedelta(days=ADS_REFRESH_DAYS)
    except (KeyError, ValueError, TypeError):
        return False


def ads_query(query, token):
    global ADS_LIMITED, ADS_REQUESTS, LAST_ADS
    if ADS_LIMITED or ADS_REQUESTS >= ADS_MAX_REQUESTS:
        return None
    elapsed = time.monotonic() - LAST_ADS
    if ADS_REQUESTS and ADS_PAUSE_SECONDS > elapsed:
        time.sleep(ADS_PAUSE_SECONDS - elapsed)
    url = ADS_API_URL + "?" + urlencode({
        "q": query, "fl": "bibcode,doi,citation_count", "rows": 10})
    request = Request(url, headers={
        "Authorization": f"Bearer {token}", "Accept": "application/json",
        "User-Agent": USER_AGENT})
    for attempt in range(2):
        ADS_REQUESTS += 1
        LAST_ADS = time.monotonic()
        try:
            with urlopen(request, timeout=45) as response:
                payload = json.load(response)
            docs = (payload.get("response") or {}).get("docs")
            if not isinstance(docs, list):
                raise RuntimeError("Malformed NASA ADS response; not overwriting cache")
            return docs
        except HTTPError as error:
            if error.code == 429:
                ADS_LIMITED = True
                print("WARNING: NASA ADS returned HTTP 429. No further ADS queries "
                      "will be attempted this run; preserving previously saved counts.")
                return None
            if error.code in (401, 403):
                raise RuntimeError("NASA ADS authentication failure: verify ADS_API_TOKEN") from error
            if error.code not in (500, 502, 503, 504) or attempt == 1:
                print(f"WARNING: ADS HTTP {error.code}; using saved metadata.")
                return None
        except (URLError, TimeoutError, ConnectionError) as error:
            if attempt == 1:
                print(f"WARNING: ADS unavailable ({type(error).__name__}); using saved metadata")
                return None
        time.sleep(2 * (attempt + 1))
    return None


def get_ads_metadata(doi, bibcode, token):
    doi, bibcode = normalize_doi(doi), str(bibcode or "").strip()
    keys = keys_for(doi, bibcode)
    if not keys:
        return {}
    old = cached_metadata(doi, bibcode)
    if old and cache_fresh(old):
        return old
    if ADS_LIMITED or ADS_REQUESTS >= ADS_MAX_REQUESTS:
        return old or {}
    # Query bibcode first, then DOI. Stop immediately when quota is exhausted.
    for field, value in (("bibcode", bibcode), ("doi", doi)):
        if not value:
            continue
        escaped = value.replace("\\", "\\\\").replace('"', '\\"')
        docs = ads_query(f'{field}:"{escaped}"', token)
        if docs is None:
            return old or {}
        for doc in docs:
            found_bib = str(doc.get("bibcode", ""))
            found_dois = doc.get("doi") or []
            if isinstance(found_dois, str):
                found_dois = [found_dois]
            if field == "bibcode" and found_bib.casefold() != value.casefold():
                continue
            if field == "doi" and value.casefold() not in {
                    normalize_doi(x).casefold() for x in found_dois}:
                continue
            count = doc.get("citation_count")
            new = {"bibcode": found_bib,
                   "citation_count": "" if count is None else count,
                   "checked_at": datetime.now(timezone.utc).isoformat(),
                   "source": "NASA ADS"}
            for key in keys_for(doi, bibcode) + keys_for("", found_bib):
                ADS_CACHE[key] = new
            return new
    # A valid no-match should be cached too, to avoid repeated ADS requests
    # every day. An actual HTTP error takes an earlier return above instead.
    if old:
        return old
    negative = {"bibcode": bibcode, "citation_count": "",
                "checked_at": datetime.now(timezone.utc).isoformat(),
                "source": "NASA ADS: no matching record"}
    for key in keys:
        ADS_CACHE[key] = negative
    return negative


def process_researcher(researcher, token):
    name, orcid = researcher["name"], researcher["orcid"]
    if not re.fullmatch(r"\d{4}-\d{4}-\d{4}-[\dX]{4}", orcid):
        raise ValueError(f"Invalid ORCID: {orcid}")
    print(f"Processing {name} ({orcid})", flush=True)
    previous = read_existing(orcid)
    old_by_doi, old_by_title = previous_index(previous)
    try:
        groups = fetch_orcid_works(orcid)
    except (HTTPError, URLError, TimeoutError, ValueError) as error:
        if previous:
            print(f"WARNING: ORCID unavailable for {name}; keeping old CSV ({type(error).__name__})")
            return
        raise RuntimeError(f"ORCID unavailable for {name}, no prior CSV to preserve") from error
    if not groups:
        if previous:
            print(f"WARNING: ORCID currently shows zero works for {name}; "
                  "preserving their previous non-empty publication CSV.")
            return
        print(f"{name} has no public ORCID works (valid empty profile)")
    rows, seen_dois, seen_titles = [], set(), set()
    for group in groups:
        works = group.get("work-summary") or []
        if not works:
            continue
        work = max(works, key=lambda w: (
            bool((w.get("publication-date") or {}).get("year")),
            bool(w.get("journal-title"))))
        title = clean_text(((work.get("title") or {}).get("title") or {}).get("value"))
        if not title:
            continue
        year = ((work.get("publication-date") or {}).get("year") or {}).get("value") or ""
        journal = clean_text((work.get("journal-title") or {}).get("value"))
        doi = normalize_doi(get_identifier(group, "doi"))
        bib = get_identifier(group, "bibcode")
        doi_k = doi.casefold()
        title_k = (str(year), title_key(title))
        if (doi_k and doi_k in seen_dois) or title_k in seen_titles:
            continue
        if doi_k:
            seen_dois.add(doi_k)
        seen_titles.add(title_k)
        earlier = old_by_doi.get(doi_k) if doi_k else None
        earlier = earlier or old_by_title.get(title_k)
        seed_cache(doi, bib, earlier)
        ads = get_ads_metadata(doi, bib, token)
        count = ads.get("citation_count", "")
        if count == "" and earlier:
            count = earlier.get("Citation (ADS)", "")
        result_bib = bib or ads.get("bibcode", "")
        doi_url = "https://doi.org/" + quote(doi, safe="/") if doi else ""
        ads_url = ("https://ui.adsabs.harvard.edu/abs/" + quote(result_bib, safe="")
                   + "/abstract") if result_bib else ""
        if not ads_url and earlier:
            ads_url = earlier.get("ADS URL", "")
        rows.append({"Year": year, "Title": html.escape(title, quote=False),
                     "Journal": html.escape(journal, quote=False),
                     "Citation (ADS)": count, "DOI URL": doi_url, "ADS URL": ads_url})
    if groups and not rows:
        raise RuntimeError(f"Malformed ORCID works for {name}; old CSV is preserved")
    rows.sort(key=lambda r: (-int(r["Year"]) if str(r["Year"]).isdigit() else 0,
                             r["Title"].casefold()))
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    output = OUTPUT_DIR / f"{orcid}.csv"
    temp = output.with_name(output.name + ".tmp")
    with temp.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=COLUMNS)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(temp, output)
    print(f"Saved {len(rows)} publications for {name} "
          f"({sum(str(row['Citation (ADS)']) != '' for row in rows)} with ADS counts)")
    save_ads_cache()  # save progress even if another researcher encounters an error


def main():
    token = os.environ.get("ADS_API_TOKEN")
    if not token:
        raise RuntimeError("Missing ADS_API_TOKEN secret")
    load_ads_cache()
    payload = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
    researchers = payload["researchers"]
    print(f"ORCID updater: at most {ADS_MAX_REQUESTS} new ADS requests per run; "
          f"metadata refreshed every {ADS_REFRESH_DAYS} days.")
    for person in researchers:
        process_researcher(person, token)
    save_ads_cache()
    print(f"Complete. ADS requests: {ADS_REQUESTS}; ADS limited: {ADS_LIMITED}. "
          "Existing citation data were retained when ADS was unavailable.")


if __name__ == "__main__":
    main()
