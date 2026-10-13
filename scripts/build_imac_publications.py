import csv
import html
import json
import os
import re
import unicodedata

from collections import defaultdict
from datetime import datetime, timezone
from difflib import SequenceMatcher
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urlencode
from urllib.request import Request, urlopen


# ==================================================
# Configuration
# ==================================================

ROOT = Path(__file__).resolve().parent.parent

SOURCE = ROOT / "docs" / "publications"
OUTPUT = ROOT / "docs" / "imac"
CONFIG = ROOT / "researchers.json"

ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"

FIELDS = [
    "Title",
    "Authors",
    "Journal",
    "Citation (ADS)",
    "DOI URL",
    "ADS URL"
]


# ==================================================
# Text and identifier cleaning
# ==================================================

def plain(value):
    return html.unescape(
        html.unescape(str(value or ""))
    ).strip()


def title_key(value):

    text = unicodedata.normalize(
        "NFKD", plain(value)
    ).casefold()

    text = text.replace("∼", "~")
    text = text.replace(r"\alpha", "alpha")
    text = text.replace("α", "alpha")

    text = re.sub(
        r"~\s*(\d+)",
        r"\1",
        text
    )

    # Treat "90 sq deg" and "90 deg²" equally.
    text = re.sub(
        r"(\d+)\s*(?:sq(?:uare)?\s*deg(?:rees?)?|deg(?:rees?)?\s*2)",
        r"\1squaredegrees",
        text
    )

    return re.sub(r"[^a-z0-9]", "", text)


def doi_key(url):

    return unquote(
        re.sub(
            r"^https?://(?:dx\.)?doi\.org/",
            "",
            plain(url),
            flags=re.I
        )
    ).casefold()


def bibcode_from_url(url):

    match = re.search(
        r"/abs/([^/]+)",
        plain(url)
    )

    return unquote(match.group(1)) if match else ""


def preprint(row):

    journal = plain(row["Journal"]).casefold()

    return (
        "arxiv" in journal
        or doi_key(row["DOI URL"]).startswith(
            "10.48550/arxiv."
        )
    )


# ==================================================
# Read individual researcher CSV files
# ==================================================

def read_records():

    configuration = json.loads(
        CONFIG.read_text(encoding="utf-8")
    )

    researchers = configuration["researchers"]

    if not researchers:
        raise RuntimeError("No researchers configured.")

    records = []

    for person in researchers:

        file = SOURCE / f'{person["orcid"]}.csv'

        if not file.is_file():
            raise FileNotFoundError(
                f"Missing researcher CSV: {file.name}"
            )

        with file.open(
            newline="",
            encoding="utf-8-sig"
        ) as handle:

            reader = csv.DictReader(handle)

            required = {
                "Year",
                "Title",
                "Journal",
                "DOI URL",
                "ADS URL"
            }

            available = set(reader.fieldnames or [])

            if not required.issubset(available):
                raise ValueError(
                    f"Unexpected CSV columns: {file.name}"
                )

            # Support both old and new citation headers.
            if not (
                "Citation (ADS)" in available
                or "Citations" in available
            ):
                raise ValueError(
                    f"Missing citation column: {file.name}"
                )

            for row in reader:

                year = str(row["Year"]).strip()
                title = plain(row["Title"])

                if not title:
                    continue

                if not (
                    year.isdigit()
                    and len(year) == 4
                ):
                    continue

                # Normalize the citation column name.
                citation = row.get("Citation (ADS)")

                if citation is None or not str(citation).strip():
                    citation = row.get("Citations", "")

                row["Citation (ADS)"] = str(
                    citation or ""
                ).strip()

                row["Year"] = year
                row["Title"] = title
                row["Journal"] = plain(row["Journal"])

                row["researcher"] = person["name"]

                row["doi_key"] = doi_key(
                    row["DOI URL"]
                )

                row["bibcode"] = bibcode_from_url(
                    row["ADS URL"]
                )

                row["title_key"] = title_key(title)
                row["preprint"] = preprint(row)

                records.append(row)

    if not records:
        raise RuntimeError(
            "No publication records found."
        )

    return researchers, records


# ==================================================
# Identify shared and duplicate publications
# ==================================================

def same_paper(row, cluster):

    # Exact DOI match.
    if (
        row["doi_key"]
        and row["doi_key"] in cluster["dois"]
    ):
        return True

    # Exact ADS bibcode match.
    if (
        row["bibcode"]
        and row["bibcode"] in cluster["bibcodes"]
    ):
        return True

    # Compare normalized titles.
    key = row["title_key"]

    if len(key) < 35:
        return False

    for other in cluster["records"]:

        if abs(
            int(row["Year"]) - int(other["Year"])
        ) > 2:
            continue

        other_key = other["title_key"]

        if key == other_key:
            return True

        # Conservative fuzzy matching for formatting
        # differences between preprint and journal titles.
        if (
            len(other_key) >= 35
            and re.findall(r"\d+", key)
            == re.findall(r"\d+", other_key)
            and SequenceMatcher(
                None, key, other_key
            ).ratio() >= 0.985
        ):
            return True

    return False


def collapse(records):

    clusters = []

    for row in records:

        target = next(
            (
                cluster
                for cluster in clusters
                if same_paper(row, cluster)
            ),
            None
        )

        if target is None:

            target = {
                "records": [],
                "researchers": set(),
                "dois": set(),
                "bibcodes": set()
            }

            clusters.append(target)

        target["records"].append(row)

        target["researchers"].add(
            row["researcher"]
        )

        if row["doi_key"]:
            target["dois"].add(row["doi_key"])

        if row["bibcode"]:
            target["bibcodes"].add(row["bibcode"])

    return clusters


# ==================================================
# Prefer journal publications over preprints
# ==================================================

def best_record(records):

    def score(row):

        citation = str(
            row["Citation (ADS)"]
        ).strip()

        return (
            not row["preprint"],
            bool(row["Journal"]),
            bool(row["doi_key"]),
            bool(row["bibcode"]),
            int(citation) if citation.isdigit() else -1
        )

    return max(records, key=score)


# ==================================================
# Retrieve authors from NASA ADS
# ==================================================

def ads_authors(records, token):

    bibcodes = sorted({
        row["bibcode"]
        for row in records
        if row["bibcode"]
    })

    dois = sorted({
        row["doi_key"]
        for row in records
        if row["doi_key"] and not row["bibcode"]
    })

    lookups = (
        [("bibcode", b) for b in bibcodes]
        + [("doi", d) for d in dois]
    )

    by_bibcode = {}
    by_doi = {}

    # Batch requests to reduce ADS API usage.
    for start in range(0, len(lookups), 20):

        batch = lookups[start:start + 20]

        clauses = [
            f'{kind}:"{value.replace(chr(34), "")}"'
            for kind, value in batch
        ]

        query = " OR ".join(clauses)

        url = ADS_API + "?" + urlencode({
            "q": query,
            "fl": (
                "bibcode,doi,"
                "first_author,author_count"
            ),
            "rows": 100
        })

        request = Request(
            url,
            headers={
                "Authorization": f"Bearer {token}",
                "Accept": "application/json",
                "User-Agent": "IMAC-Publications/1.0"
            }
        )

        try:
            with urlopen(
                request,
                timeout=60
            ) as response:

                result = json.load(response)

        except HTTPError as error:

            raise RuntimeError(
                "ADS author lookup failed "
                f"(HTTP {error.code})."
            ) from None

        except (URLError, TimeoutError):

            raise RuntimeError(
                "ADS could not be reached "
                "for author metadata."
            ) from None

        response = result.get("response", {})
        docs = response.get("docs")

        if not isinstance(docs, list):
            raise RuntimeError(
                "Unexpected response from ADS."
            )

        if response.get("numFound", 0) > len(docs):
            raise RuntimeError(
                "ADS result was truncated. "
                "Publication update stopped."
            )

        for doc in docs:

            bibcode = doc.get("bibcode", "")

            if bibcode:
                by_bibcode[bibcode] = doc

            returned_dois = doc.get("doi") or []

            if isinstance(returned_dois, str):
                returned_dois = [returned_dois]

            for doi in returned_dois:
                by_doi[doi.casefold()] = doc

    return by_bibcode, by_doi


# ==================================================
# Format IMAC researcher names
# ==================================================

def imac_name(name):

    parts = name.split()

    if len(parts) > 1:
        return f"{parts[0][0]}. {parts[-1]}"

    return name


# ==================================================
# Generate combined Authors column
# ==================================================

def authors_label(cluster, metadata, order):

    members = sorted(
        cluster["researchers"],
        key=lambda name: order[name]
    )

    included = ", ".join(
        imac_name(name)
        for name in members
    )

    representative = best_record(
        cluster["records"]
    )

    bibcode = representative["bibcode"]
    doi = representative["doi_key"]

    doc = (
        metadata[0].get(bibcode)
        or metadata[1].get(doi)
    )

    # Try alternative publication editions.
    if not doc:

        for row in cluster["records"]:

            doc = (
                metadata[0].get(row["bibcode"])
                or metadata[1].get(row["doi_key"])
            )

            if doc:
                break

    if doc:

        first = doc.get("first_author") or ""

        if isinstance(first, list):
            first = first[0] if first else ""

        if first:

            surname = plain(first).split(",")[0].strip()

            count = doc.get("author_count")

            lead = surname + (
                " et al."
                if count is None or int(count) > 1
                else ""
            )

            return (
                f"{lead} "
                f"(incl. {included})"
            )

    # Do not invent first-author information.
    return f"IMAC contributors: {included}"


# ==================================================
# Create one publication row
# ==================================================

def output_row(cluster, metadata, order):

    record = best_record(cluster["records"])

    return {
        "Title": html.escape(
            record["Title"],
            quote=False
        ),
        "Authors": html.escape(
            authors_label(cluster, metadata, order),
            quote=False
        ),
        "Journal": html.escape(
            record["Journal"],
            quote=False
        ),
        "Citation (ADS)": record["Citation (ADS)"],
        "DOI URL": record["DOI URL"],
        "ADS URL": record["ADS URL"]
    }


# ==================================================
# Write CSV files for Terminalfour
# ==================================================

def write_csv(path, rows):

    temporary = path.with_suffix(".csv.tmp")

    with temporary.open(
        "w",
        newline="",
        encoding="utf-8"
    ) as handle:

        writer = csv.DictWriter(
            handle,
            fieldnames=FIELDS
        )

        writer.writeheader()
        writer.writerows(rows)

    os.replace(temporary, path)


# ==================================================
# NEW: Calculate annual publication statistics
# ==================================================

def make_summary_row(year, rows):

    # Each row represents one unique published paper
    # because duplicate publications were already
    # combined before this function is called.

    number_of_papers = len(rows)

    # Collect valid NASA ADS citation counts.
    # A blank count means unavailable information.
    # An actual zero is included in the calculation.

    citation_counts = []

    for row in rows:

        value = str(
            row["Citation (ADS)"]
        ).strip()

        if value.isdigit():
            citation_counts.append(int(value))

    total_citations = sum(citation_counts)

    papers_with_ads_data = len(citation_counts)

    # Generate a readable summary for the table.

    summary_text = (
        f"YEAR {year} SUMMARY: "
        f"{number_of_papers} published papers; "
        f"{total_citations:,} ADS citations "
        f"({papers_with_ads_data}/{number_of_papers} "
        f"papers with ADS data)"
    )

    # Use the same columns as the publication table.
    # Leave the other columns empty so the summary
    # is not confused with an additional paper.

    summary_row = {
        "Title": summary_text,
        "Authors": "",
        "Journal": "",
        "Citation (ADS)": "",
        "DOI URL": "",
        "ADS URL": ""
    }

    return summary_row, number_of_papers, total_citations


# ==================================================
# Main program
# ==================================================

def main():

    # Secret comes from GitHub Actions.
    # Never print or save the token.

    token = os.environ.get("ADS_API_TOKEN")

    if not token:
        raise RuntimeError(
            "Missing ADS_API_TOKEN GitHub Actions secret."
        )

    # --------------------------------------------------
    # Step 1: Read individual researcher publications
    # --------------------------------------------------

    researchers, records = read_records()

    # --------------------------------------------------
    # Step 2: Remove duplicate publications
    # --------------------------------------------------

    clusters = collapse(records)

    # --------------------------------------------------
    # Step 3: Retrieve first-author information
    # --------------------------------------------------

    metadata = ads_authors(records, token)

    order = {
        person["name"]: i
        for i, person in enumerate(researchers)
    }

    # --------------------------------------------------
    # Step 4: Organize publications by year
    # --------------------------------------------------

    annual = defaultdict(list)
    preprints = []

    for cluster in clusters:

        representative = best_record(
            cluster["records"]
        )

        row = output_row(
            cluster,
            metadata,
            order
        )

        if representative["preprint"]:

            # Recent arXiv preprints from the current
            # and previous calendar year.

            if int(representative["Year"]) >= (
                datetime.now(timezone.utc).year - 1
            ):
                preprints.append(row)

        else:

            annual[
                representative["Year"]
            ].append(row)

    OUTPUT.mkdir(
        parents=True,
        exist_ok=True
    )

    # --------------------------------------------------
    # Step 5: Generate yearly CSVs with statistics
    # --------------------------------------------------

    for year, rows in sorted(
        annual.items(),
        reverse=True
    ):

        # Sort publication records alphabetically.
        rows.sort(
            key=lambda r: r["Title"].casefold()
        )

        # Calculate the statistics for this year.
        summary_row, number_of_papers, total_citations = (
            make_summary_row(year, rows)
        )

        # Insert the summary before the publications.
        rows_with_summary = [summary_row] + rows

        # Keep the original filename and URL.
        file = OUTPUT / f"publications_{year}.csv"

        write_csv(
            file,
            rows_with_summary
        )

        print(
            f"{year}: "
            f"{number_of_papers} unique published papers; "
            f"{total_citations:,} ADS citations"
        )

    # --------------------------------------------------
    # Step 6: Generate recent preprints CSV
    # --------------------------------------------------

    # Preprints do not receive an annual summary row.

    preprints.sort(
        key=lambda r: r["Title"].casefold()
    )

    write_csv(
        OUTPUT / "recent_preprints.csv",
        preprints
    )

    print(
        f"Recent preprints: {len(preprints)}"
    )

    print(
        "Total unique works, including older preprints: "
        f"{len(clusters)}"
    )


if __name__ == "__main__":
    main()
