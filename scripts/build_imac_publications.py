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
                "Citation (ADS)",
                "DOI URL",
                "ADS URL"
            }

            if not required.issubset(
                reader.fieldnames or []
            ):
                raise ValueError(
                    f"Unexpected CSV columns: {file.name}"
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
                c for c in clusters
                if same_paper(row, c)
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

        return (
            not row["preprint"],
            bool(row["Journal"]),
            bool(row["doi_key"]),
            bool(row["bibcode"]),
            (
                int(row["Citation (ADS)"])
                if str(row["Citation (ADS)"]).isdigit()
                else -1
            )
        )

    return max(records, key=score)


# ==================================================
# Retrieve authors from NASA ADS
# ==================================================

def ads_authors(records, token):

    bibcodes = sorted({
        r["bibcode"]
        for r in records
        if r["bibcode"]
    })

    dois = sorted({
        r["doi_key"]
        for r in records
        if r["doi_key"] and not r["bibcode"]
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

    researchers, records = read_records()

    clusters = collapse(records)

    metadata = ads_authors(records, token)

    order = {
        person["name"]: i
        for i, person in enumerate(researchers)
    }

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

    # One CSV per publication year.
    for year, rows in sorted(
        annual.items(),
        reverse=True
    ):

        rows.sort(
            key=lambda r: r["Title"].casefold()
        )

        file = OUTPUT / f"publications_{year}.csv"

        write_csv(file, rows)

        print(
            f"{year}: {len(rows)} "
            "unique published records"
        )

    # Separate CSV for recent unpublished preprints.
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
