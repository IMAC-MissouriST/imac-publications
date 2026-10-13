import csv
import html
import json
import os
import re

from pathlib import Path
from urllib.request import Request, urlopen
from urllib.parse import quote


# ==================================================
# Configuration
# ==================================================

BASE_DIR = Path(__file__).resolve().parent.parent

CONFIG_FILE = BASE_DIR / "researchers.json"

# Store publication files here so they can later
# be hosted directly using GitHub Pages.
OUTPUT_DIR = BASE_DIR / "docs" / "publications"


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
# Extract DOI and NASA ADS bibcode
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
# Process ONE researcher's publications
# ==================================================

def process_researcher(researcher):

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

    # Avoid silently replacing an existing CSV
    # with an empty file after an unexpected response.
    if not groups:
        raise RuntimeError(
            f"No public publication groups returned for {name}. "
            "Check the ORCID record before proceeding."
        )

    publications = []

    seen_dois = set()
    seen_titles = set()

    for group in groups:

        works = group.get("work-summary") or []

        if not works:
            continue

        # Prefer a work with complete publication metadata.
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

        doi = get_identifier(group, "doi")
        bibcode = get_identifier(group, "bibcode")

        # Normalize DOI if needed.
        doi = re.sub(
            r"^https?://(?:dx\.)?doi\.org/",
            "",
            doi.strip(),
            flags=re.IGNORECASE
        )

        # Remove duplicates only within THIS
        # researcher's publication list.
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

        # Escape HTML-sensitive characters for T4.
        publications.append({
            "Year": year,
            "Title": html.escape(title, quote=False),
            "Journal": html.escape(journal, quote=False),
            "DOI": doi,
            "DOI URL": doi_url,
            "ADS URL": ads_url
        })

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
    # Create an individual CSV file
    # ==================================================

    OUTPUT_DIR.mkdir(
        parents=True,
        exist_ok=True
    )

    output_file = OUTPUT_DIR / f"{orcid}.csv"
    temporary_file = OUTPUT_DIR / f"{orcid}.csv.tmp"

    columns = [
        "Year",
        "Title",
        "Journal",
        "DOI",
        "DOI URL",
        "ADS URL"
    ]

    with open(
        temporary_file,
        "w",
        newline="",
        encoding="utf-8"
    ) as f:

        writer = csv.DictWriter(
            f,
            fieldnames=columns
        )

        writer.writeheader()
        writer.writerows(publications)

    # Replace the old CSV only after successfully
    # generating the complete new one.
    os.replace(temporary_file, output_file)

    print(f"Successfully generated: {output_file}")
    print(f"Number of publications: {len(publications)}")


# ==================================================
# Main program
# ==================================================

def main():

    with open(
        CONFIG_FILE,
        "r",
        encoding="utf-8"
    ) as f:

        config = json.load(f)

    researchers = config["researchers"]

    print("=" * 50)
    print("IMAC ORCID Publication Updater")
    print("=" * 50)

    for researcher in researchers:

        process_researcher(researcher)

    print("\nAll researchers processed successfully!")


if __name__ == "__main__":
    main()
