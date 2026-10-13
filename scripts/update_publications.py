import csv
import html
import json
import os
import re

from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urlencode
from urllib.request import Request, urlopen


# ==================================================
# Configuration
# ==================================================

BASE_DIR = Path(__file__).resolve().parent.parent

CONFIG_FILE = BASE_DIR / "researchers.json"

OUTPUT_DIR = BASE_DIR / "docs" / "publications"

ADS_API_URL = "https://api.adsabs.harvard.edu/v1/search/query"

# Reuse ADS results for publications shared by researchers.
ADS_CACHE = {}

# Final column order for Terminalfour.
COLUMNS = [
    "Year",
    "Title",
    "Journal",
    "Citation (ADS)",
    "DOI URL",
    "ADS URL"
]


# ==================================================
# Clean publication titles and journal names
# ==================================================

def clean_text(value):

    if not value:
        return ""

    text = html.unescape(str(value))

    # Convert HTML superscripts into Unicode.
    superscripts = str.maketrans(
        "0123456789",
        "⁰¹²³⁴⁵⁶⁷⁸⁹"
    )

    text = re.sub(
        r"<sup\b[^>]*>(.*?)</sup>",
        lambda m: m.group(1).translate(superscripts),
        text,
        flags=re.IGNORECASE
    )

    # Remove common formatting tags.
    text = re.sub(
        r"</?(?:i|em|b|strong|span|sub)\b[^>]*>",
        "",
        text,
        flags=re.IGNORECASE
    )

    return " ".join(text.split())


# ==================================================
# Retrieve public works from ORCID
# ==================================================

def fetch_orcid_works(orcid):

    url = f"https://pub.orcid.org/v3.0/{orcid}/works"

    request = Request(
        url,
        headers={
            "Accept": "application/vnd.orcid+json",
            "User-Agent": "IMAC-Publications-Updater/1.0"
        }
    )

    with urlopen(request, timeout=60) as response:
        return json.load(response)


# ==================================================
# Extract identifiers from ORCID
# ==================================================

def get_identifier(group, id_type):

    sources = [group] + (group.get("work-summary") or [])

    for source in sources:

        external_ids = (
            (source.get("external-ids") or {})
            .get("external-id") or []
        )

        for item in external_ids:

            if (
                item.get("external-id-type") or ""
            ).lower() == id_type:

                return (
                    (item.get("external-id-normalized") or {})
                    .get("value")
                    or item.get("external-id-value")
                    or ""
                )

    return ""


# ==================================================
# Normalize DOI
# ==================================================

def normalize_doi(doi):

    if not doi:
        return ""

    doi = str(doi).strip()

    doi = re.sub(
        r"^https?://(?:dx\.)?doi\.org/",
        "",
        doi,
        flags=re.IGNORECASE
    )

    doi = re.sub(
        r"^doi:\s*",
        "",
        doi,
        flags=re.IGNORECASE
    )

    return doi.strip()


# ==================================================
# Query NASA ADS
# ==================================================

def search_ads(query, token):

    parameters = urlencode({
        "q": query,
        "fl": "bibcode,doi,citation_count",
        "rows": 10
    })

    url = f"{ADS_API_URL}?{parameters}"

    request = Request(
        url,
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/json",
            "User-Agent": "IMAC-Publications-Updater/1.0"
        }
    )

    try:

        with urlopen(request, timeout=45) as response:
            data = json.load(response)

    except HTTPError as error:

        if error.code == 429:
            raise RuntimeError(
                "NASA ADS API rate limit reached. "
                "Try running the workflow again later."
            ) from error

        if error.code in (401, 403):
            raise RuntimeError(
                "NASA ADS API authentication or permission error. "
                "Check the ADS_API_TOKEN repository secret."
            ) from error

        raise RuntimeError(
            f"NASA ADS API request failed: HTTP {error.code}"
        ) from error

    except (URLError, TimeoutError) as error:

        raise RuntimeError(
            "Could not connect to NASA ADS. "
            "Existing published CSV files will not be committed "
            "with incomplete citation data."
        ) from error

    response = data.get("response")

    if not isinstance(response, dict):
        raise RuntimeError(
            "NASA ADS returned an unexpected response."
        )

    documents = response.get("docs")

    if not isinstance(documents, list):
        raise RuntimeError(
            "NASA ADS response did not contain a valid document list."
        )

    return documents


# ==================================================
# Get ADS citation count for one publication
# ==================================================

def get_ads_metadata(doi, bibcode, token):

    doi = normalize_doi(doi)

    bibcode = str(bibcode or "").strip()

    # Prefer ADS bibcode, then DOI.
    identifiers = []

    if bibcode:
        identifiers.append(("bibcode", bibcode))

    if doi:
        identifiers.append(("doi", doi))

    if not identifiers:
        return {}

    # Check in-memory cache.
    cache_keys = [
        (field, value.casefold())
        for field, value in identifiers
    ]

    for key in cache_keys:
        if key in ADS_CACHE:
            return ADS_CACHE[key]

    result = {}

    for field, value in identifiers:

        # Escape special characters inside quoted ADS queries.
        escaped_value = (
            value.replace("\\", "\\\\")
                 .replace('"', '\\"')
        )

        query = f'{field}:"{escaped_value}"'

        documents = search_ads(query, token)

        if not documents:
            continue

        # Match returned identifiers to the requested paper.
        for document in documents:

            returned_bibcode = document.get("bibcode", "")

            returned_dois = document.get("doi") or []

            if isinstance(returned_dois, str):
                returned_dois = [returned_dois]

            if field == "bibcode":

                if returned_bibcode.casefold() != value.casefold():
                    continue

            elif field == "doi":

                returned_doi_keys = {
                    normalize_doi(item).casefold()
                    for item in returned_dois
                }

                if value.casefold() not in returned_doi_keys:
                    continue

            citation_count = document.get("citation_count")

            # An ADS count of zero is valid.
            # Missing citation metadata remains blank.
            if citation_count is None:
                citation_count = ""

            result = {
                "bibcode": returned_bibcode,
                "citation_count": citation_count
            }

            break

        if result:
            break

    # Cache matches and unsuccessful lookups.
    for key in cache_keys:
        ADS_CACHE[key] = result

    # Also cache the ADS bibcode returned by a DOI lookup.
    if result.get("bibcode"):
        ADS_CACHE[
            ("bibcode", result["bibcode"].casefold())
        ] = result

    return result


# ==================================================
# Process ONE researcher's publications
# ==================================================

def process_researcher(researcher, token):

    name = researcher["name"]
    orcid = researcher["orcid"]

    if not re.fullmatch(
        r"\d{4}-\d{4}-\d{4}-[\dX]{4}",
        orcid
    ):
        raise ValueError(f"Invalid ORCID format: {orcid}")

    print(f"\nProcessing researcher: {name}")
    print(f"ORCID: {orcid}")

    data = fetch_orcid_works(orcid)

    groups = data.get("group") or []

    if not groups:
        raise RuntimeError(
            f"No public publication groups returned for {name}. "
            "Existing publication files should not be overwritten."
        )

    publications = []

    seen_dois = set()
    seen_titles = set()

    for group in groups:

        works = group.get("work-summary") or []

        if not works:
            continue

        # Prefer the record with more complete metadata.
        work = max(
            works,
            key=lambda w: (
                bool((w.get("publication-date") or {}).get("year")),
                bool(w.get("journal-title"))
            )
        )

        title = clean_text(
            ((work.get("title") or {}).get("title") or {})
            .get("value")
        )

        if not title:
            continue

        date = work.get("publication-date") or {}

        year = (
            (date.get("year") or {}).get("value")
            or ""
        )

        journal = clean_text(
            (work.get("journal-title") or {}).get("value")
        )

        # Identifiers from ORCID.
        doi = normalize_doi(
            get_identifier(group, "doi")
        )

        bibcode = get_identifier(group, "bibcode")

        # ------------------------------------------
        # Remove duplicates within this researcher
        # ------------------------------------------

        doi_key = doi.casefold()

        title_key = (
            str(year),
            re.sub(r"\W+", "", title).casefold()
        )

        if (
            (doi_key and doi_key in seen_dois)
            or title_key in seen_titles
        ):
            continue

        if doi_key:
            seen_dois.add(doi_key)

        seen_titles.add(title_key)

        # ------------------------------------------
        # Retrieve NASA ADS citation count
        # ------------------------------------------

        ads_metadata = get_ads_metadata(
            doi=doi,
            bibcode=bibcode,
            token=token
        )

        citation_count = ads_metadata.get(
            "citation_count",
            ""
        )

        # Use the ADS bibcode when ORCID lacks one.
        if not bibcode:
            bibcode = ads_metadata.get("bibcode", "")

        # ------------------------------------------
        # Generate DOI and ADS links
        # ------------------------------------------

        doi_url = (
            "https://doi.org/" + quote(doi, safe="/")
            if doi else ""
        )

        ads_url = (
            "https://ui.adsabs.harvard.edu/abs/"
            + quote(bibcode, safe="")
            + "/abstract"
            if bibcode else ""
        )

        # ------------------------------------------
        # Store publication information
        # ------------------------------------------

        publications.append({
            "Year": year,
            "Title": html.escape(title, quote=False),
            "Journal": html.escape(journal, quote=False),
            "Citation (ADS)": citation_count,
            "DOI URL": doi_url,
            "ADS URL": ads_url
        })

    if not publications:
        raise RuntimeError(
            f"No valid publications found for {name}."
        )

    # ==================================================
    # Sort from newest to oldest
    # ==================================================

    publications.sort(
        key=lambda p: (
            -int(p["Year"])
            if str(p["Year"]).isdigit()
            else 0,
            p["Title"].casefold()
        )
    )

    # ==================================================
    # Create an individual CSV
    # ==================================================

    OUTPUT_DIR.mkdir(
        parents=True,
        exist_ok=True
    )

    output_file = OUTPUT_DIR / f"{orcid}.csv"
    temporary_file = OUTPUT_DIR / f"{orcid}.csv.tmp"

    with open(
        temporary_file,
        "w",
        newline="",
        encoding="utf-8"
    ) as f:

        writer = csv.DictWriter(
            f,
            fieldnames=COLUMNS
        )

        writer.writeheader()
        writer.writerows(publications)

    # Replace the old CSV only after successful retrieval.
    os.replace(temporary_file, output_file)

    matched_count = sum(
        publication["Citation (ADS)"] != ""
        for publication in publications
    )

    print(f"Successfully generated: {output_file}")
    print(f"Number of publications: {len(publications)}")
    print(f"Publications with ADS citation data: {matched_count}")


# ==================================================
# Main program
# ==================================================

def main():

    # Token comes from GitHub Actions Secrets.
    # Never print or save the token in output files.
    token = os.environ.get("ADS_API_TOKEN")

    if not token:
        raise RuntimeError(
            "ADS_API_TOKEN is missing. "
            "Configure it under GitHub Actions repository secrets."
        )

    with open(
        CONFIG_FILE,
        "r",
        encoding="utf-8"
    ) as f:

        config = json.load(f)

    researchers = config["researchers"]

    print("=" * 50)
    print("IMAC ORCID + NASA ADS Publication Updater")
    print("=" * 50)

    for researcher in researchers:
        process_researcher(researcher, token)

    print("\nAll researchers processed successfully!")


if __name__ == "__main__":
    main()
