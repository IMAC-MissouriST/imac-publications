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


# ============================================================
# CONFIGURATION
# ============================================================

ROOT = Path(__file__).resolve().parent.parent

SOURCE = ROOT / "docs" / "publications"

LIVE_OUTPUT = ROOT / "docs" / "imac"

PREVIEW_OUTPUT = ROOT / "docs" / "imac_affiliation_preview"

CONFIG = ROOT / "researchers.json"

ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"

# IMAC was established in 2019.
# This controls the period used for the overall statistics.
START_YEAR = 2019

# IMPORTANT:
# Keep "preview" until we verify the new affiliation filtering.
# Later we can change this to "live".
OUTPUT_MODE = os.environ.get(
    "IMAC_OUTPUT_MODE",
    "preview"
).strip().lower()

FIELDS = [
    "Title",
    "Authors",
    "Journal",
    "Citation (ADS)",
    "DOI URL",
    "ADS URL"
]


# ============================================================
# AFFILIATION MATCHING
# ============================================================

# Accepted institutional names.
#
# We do NOT accept "S&T" alone because it may refer
# to an unrelated institution.
#
# An explicit standalone "IMAC" is accepted, but
# the affiliation review report should be checked
# for ambiguous abbreviations.

AFFILIATION_PATTERNS = [
    re.compile(
        r"\bMissouri\s+(?:University\s+of\s+)?"
        r"Science\s*(?:and|&)\s*Technology\b",
        re.IGNORECASE
    ),

    re.compile(
        r"\bMissouri\s+S\s*(?:&|and)\s*T\b",
        re.IGNORECASE
    ),

    re.compile(
        r"\bInstitute\s+for\s+Multi[\s-]*messenger\s+"
        r"Astrophysics\s*(?:and|&)\s*Cosmology\b",
        re.IGNORECASE
    ),

    re.compile(
        r"\bIMAC\b"
    )
]


# ============================================================
# TEXT CLEANING
# ============================================================

def plain(value):

    return html.unescape(
        html.unescape(str(value or ""))
    ).strip()


def title_key(value):

    text = unicodedata.normalize(
        "NFKD",
        plain(value)
    ).casefold()

    text = text.replace("∼", "~")
    text = text.replace(r"\alpha", "alpha")
    text = text.replace("α", "alpha")

    text = re.sub(
        r"~\s*(\d+)",
        r"\1",
        text
    )

    text = re.sub(
        r"(\d+)\s*(?:sq(?:uare)?\s*deg(?:rees?)?|"
        r"deg(?:rees?)?\s*2)",
        r"\1squaredegrees",
        text
    )

    return re.sub(
        r"[^a-z0-9]",
        "",
        text
    )


def doi_key(url):

    value = plain(url)

    value = re.sub(
        r"^https?://(?:dx\.)?doi\.org/",
        "",
        value,
        flags=re.I
    )

    value = re.sub(
        r"^doi:\s*",
        "",
        value,
        flags=re.I
    )

    return unquote(value).casefold()


def bibcode_from_url(url):

    match = re.search(
        r"/abs/([^/]+)",
        plain(url)
    )

    return unquote(match.group(1)) if match else ""


def preprint(row):

    journal = plain(row["Journal"]).casefold()
    title = plain(row["Title"]).casefold()

    return (
        "arxiv" in journal
        or doi_key(row["DOI URL"]).startswith(
            "10.48550/arxiv."
        )
        or title.startswith("arxiv:")
    )


# ============================================================
# READ INDIVIDUAL RESEARCHER PUBLICATION FILES
# ============================================================

def read_records():

    configuration = json.loads(
        CONFIG.read_text(encoding="utf-8")
    )

    researchers = configuration["researchers"]

    if not researchers:
        raise RuntimeError(
            "No researchers configured."
        )

    records = []

    for person in researchers:

        orcid = person["orcid"]

        file = SOURCE / f"{orcid}.csv"

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
                    f"Unexpected columns in {file.name}"
                )

            if not (
                "Citation (ADS)" in available
                or "Citations" in available
            ):
                raise ValueError(
                    f"Missing citation column in {file.name}"
                )

            for row in reader:

                year = str(
                    row.get("Year", "")
                ).strip()

                title = plain(
                    row.get("Title", "")
                )

                if not title:
                    continue

                if not (
                    year.isdigit()
                    and len(year) == 4
                ):
                    continue

                citation = row.get("Citation (ADS)")

                if citation is None or not str(citation).strip():
                    citation = row.get("Citations", "")

                row["Citation (ADS)"] = str(
                    citation or ""
                ).strip()

                row["Year"] = year
                row["Title"] = title

                row["Journal"] = plain(
                    row.get("Journal", "")
                )

                row["researcher"] = person["name"]

                row["doi_key"] = doi_key(
                    row.get("DOI URL", "")
                )

                row["bibcode"] = bibcode_from_url(
                    row.get("ADS URL", "")
                )

                row["title_key"] = title_key(title)

                row["preprint"] = preprint(row)

                records.append(row)

    if not records:
        raise RuntimeError(
            "No publication records were found."
        )

    return researchers, records


# ============================================================
# IDENTIFY DUPLICATE PUBLICATIONS
# ============================================================

def same_paper(row, cluster):

    if (
        row["doi_key"]
        and row["doi_key"] in cluster["dois"]
    ):
        return True

    if (
        row["bibcode"]
        and row["bibcode"] in cluster["bibcodes"]
    ):
        return True

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

        if (
            len(other_key) >= 35
            and re.findall(r"\d+", key)
            == re.findall(r"\d+", other_key)
            and SequenceMatcher(
                None,
                key,
                other_key
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


# ============================================================
# PREFER PUBLISHED PAPERS OVER PREPRINTS
# ============================================================

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


# ============================================================
# NASA ADS METADATA
#
# We now request "aff" as well as author information.
# ============================================================

def ads_metadata(records, token):

    bibcodes = sorted({
        row["bibcode"]
        for row in records
        if row["bibcode"]
    })

    dois = sorted({
        row["doi_key"]
        for row in records
        if row["doi_key"]
    })

    lookups = (
        [("bibcode", value) for value in bibcodes]
        + [("doi", value) for value in dois]
    )

    by_bibcode = {}
    by_doi = {}

    for start in range(0, len(lookups), 20):

        batch = lookups[start:start + 20]

        clauses = []

        for kind, value in batch:

            safe_value = (
                value.replace("\\", "\\\\")
                .replace('"', '\\"')
            )

            clauses.append(
                f'{kind}:"{safe_value}"'
            )

        query = " OR ".join(clauses)

        url = ADS_API + "?" + urlencode({
            "q": query,
            "fl": (
                "bibcode,doi,first_author,"
                "author_count,aff"
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
                "NASA ADS metadata request failed "
                f"(HTTP {error.code})."
            ) from None

        except (URLError, TimeoutError):

            raise RuntimeError(
                "NASA ADS could not be reached."
            ) from None

        response = result.get("response", {})

        docs = response.get("docs")

        if not isinstance(docs, list):
            raise RuntimeError(
                "Unexpected NASA ADS response."
            )

        if response.get("numFound", 0) > len(docs):
            raise RuntimeError(
                "NASA ADS results were truncated. "
                "Update stopped to avoid incomplete metadata."
            )

        for doc in docs:

            bibcode = doc.get("bibcode", "")

            if bibcode:
                by_bibcode[bibcode] = doc

            returned_dois = doc.get("doi") or []

            if isinstance(returned_dois, str):
                returned_dois = [returned_dois]

            for doi in returned_dois:
                by_doi[doi_key(doi)] = doc

    return by_bibcode, by_doi


# ============================================================
# GET ADS DOCUMENTS FOR A PUBLICATION CLUSTER
# ============================================================

def documents_for_cluster(cluster, metadata):

    by_bibcode, by_doi = metadata

    documents = []
    seen = set()

    for row in cluster["records"]:

        candidates = [
            by_bibcode.get(row["bibcode"]),
            by_doi.get(row["doi_key"])
        ]

        for doc in candidates:

            if not doc:
                continue

            bibcode = doc.get("bibcode", "")

            if bibcode and bibcode in seen:
                continue

            if bibcode:
                seen.add(bibcode)

            documents.append(doc)

    return documents


# ============================================================
# CHECK IMAC / MISSOURI S&T AFFILIATION
# ============================================================

def check_affiliation(cluster, metadata):

    documents = documents_for_cluster(
        cluster,
        metadata
    )

    if not documents:
        return (
            False,
            "No matching ADS record",
            ""
        )

    affiliations_found = []

    for doc in documents:

        affiliations = doc.get("aff") or []

        if isinstance(affiliations, str):
            affiliations = [affiliations]

        for affiliation in affiliations:

            value = plain(affiliation)

            if value.casefold() in {
                "",
                "-",
                "n/a",
                "none",
                "null",
                "unknown",
                "not available"
            }:
                continue

            affiliations_found.append(value)

            for pattern in AFFILIATION_PATTERNS:

                if pattern.search(value):

                    return (
                        True,
                        "IMAC / Missouri S&T affiliation",
                        value
                    )

    if affiliations_found:

        return (
            False,
            "Different affiliation in ADS",
            " | ".join(affiliations_found)[:1000]
        )

    return (
        False,
        "No usable affiliation in ADS",
        ""
    )


# ============================================================
# FORMAT IMAC RESEARCHER NAMES
# ============================================================

def imac_name(name):

    parts = name.split()

    if len(parts) > 1:
        return f"{parts[0][0]}. {parts[-1]}"

    return name


# ============================================================
# GENERATE AUTHORS COLUMN
# ============================================================

def authors_label(cluster, metadata, order):

    members = sorted(
        cluster["researchers"],
        key=lambda name: order[name]
    )

    included = ", ".join(
        imac_name(name)
        for name in members
    )

    documents = documents_for_cluster(
        cluster,
        metadata
    )

    if documents:

        doc = documents[0]

        first = doc.get("first_author") or ""

        if isinstance(first, list):
            first = first[0] if first else ""

        if first:

            surname = plain(first).split(",")[0].strip()

            count = doc.get("author_count")

            try:
                multiple = (
                    count is None
                    or int(count) > 1
                )
            except (TypeError, ValueError):
                multiple = True

            lead = surname + (
                " et al." if multiple else ""
            )

            return (
                f"{lead} "
                f"(incl. {included})"
            )

    return f"IMAC contributors: {included}"


# ============================================================
# GENERATE ONE PUBLICATION ROW
# ============================================================

def output_row(cluster, metadata, order):

    record = best_record(
        cluster["records"]
    )

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


# ============================================================
# WRITE CSV FILE
# ============================================================

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

    os.replace(
        temporary,
        path
    )


# ============================================================
# GENERATE OVERALL IMAC STATISTICS
# ============================================================

def create_summary(output_dir, annual):

    current_year = datetime.now(timezone.utc).year

    # All affiliation-verified published papers
    # in the selected period.
    papers = [
        row
        for year, rows in annual.items()
        if START_YEAR <= int(year) <= current_year
        for row in rows
    ]

    total_papers = len(papers)

    citation_counts = []

    for paper in papers:

        value = str(
            paper["Citation (ADS)"]
        ).strip()

        if value.isdigit():
            citation_counts.append(int(value))

    total_citations = sum(citation_counts)

    papers_with_ads_data = len(citation_counts)

    # --------------------------------------------------
    # Human-readable summary
    # --------------------------------------------------

    summary = (
        f"IMAC has published a total of "
        f"{total_papers:,} articles, "
        f"which have received "
        f"{total_citations:,} citations "
        f"according to NASA ADS."
    )

    note = (
        f"Period: {START_YEAR}–{current_year}. "
        f"Includes publications with verified "
        f"IMAC or Missouri S&T affiliations. "
        f"ADS citation data available for "
        f"{papers_with_ads_data} of "
        f"{total_papers} articles."
    )

    # --------------------------------------------------
    # 1. Write a simple CSV version
    # --------------------------------------------------

    csv_file = output_dir / "summary_statistics.csv"

    with csv_file.open(
        "w",
        newline="",
        encoding="utf-8"
    ) as handle:

        writer = csv.writer(handle)

        writer.writerow([
            "IMAC Publication Summary"
        ])

        writer.writerow([
            summary
        ])

    # --------------------------------------------------
    # 2. Write JSON version for dynamic display
    # --------------------------------------------------

    json_file = output_dir / "summary.json"

    json_file.write_text(
        json.dumps(
            {
                "start_year": START_YEAR,
                "end_year": current_year,
                "published_papers": total_papers,
                "total_ads_citations": total_citations,
                "papers_with_ads_data": papers_with_ads_data,
                "summary": summary,
                "note": note
            },
            indent=2
        ),
        encoding="utf-8"
    )

    # --------------------------------------------------
    # 3. Write HTML version for possible embedding
    # --------------------------------------------------

    summary_html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
body {{
    margin: 0;
    padding: 16px;
    font-family: Arial, sans-serif;
    text-align: center;
    color: #003b49;
}}
.summary {{
    font-size: 22px;
    font-weight: 600;
    line-height: 1.6;
}}
.note {{
    font-size: 13px;
    color: #555;
    margin-top: 12px;
}}
</style>
</head>
<body>
<div class="summary">{html.escape(summary)}</div>
<div class="note">{html.escape(note)}</div>
</body>
</html>
"""

    html_file = output_dir / "summary.html"

    html_file.write_text(
        summary_html,
        encoding="utf-8"
    )

    print()
    print("OVERALL IMAC STATISTICS")
    print(summary)
    print(note)

    return total_papers


# ============================================================
# WRITE AFFILIATION REVIEW REPORT
# ============================================================

def write_review_report(output_dir, review):

    file = output_dir / "affiliation_review.csv"

    with file.open(
        "w",
        newline="",
        encoding="utf-8"
    ) as handle:

        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "Year",
                "Title",
                "Reason",
                "ADS affiliation",
                "DOI URL",
                "ADS URL"
            ]
        )

        writer.writeheader()
        writer.writerows(review)


# ============================================================
# MAIN PROGRAM
# ============================================================

def main():

    token = os.environ.get("ADS_API_TOKEN")

    if not token:
        raise RuntimeError(
            "Missing ADS_API_TOKEN GitHub Actions secret."
        )

    if OUTPUT_MODE not in {"preview", "live"}:
        raise ValueError(
            "IMAC_OUTPUT_MODE must be preview or live."
        )

    output_dir = (
        PREVIEW_OUTPUT
        if OUTPUT_MODE == "preview"
        else LIVE_OUTPUT
    )

    print("=" * 60)
    print("IMAC Publications - Affiliation Filter")
    print("=" * 60)
    print(f"Output mode: {OUTPUT_MODE}")

    # --------------------------------------------------
    # 1. Read researcher publications
    # --------------------------------------------------

    researchers, records = read_records()

    # --------------------------------------------------
    # 2. Remove duplicate publications
    # --------------------------------------------------

    clusters = collapse(records)

    # --------------------------------------------------
    # 3. Retrieve NASA ADS author and affiliation data
    # --------------------------------------------------

    metadata = ads_metadata(
        records,
        token
    )

    order = {
        person["name"]: index
        for index, person in enumerate(researchers)
    }

    annual = defaultdict(list)

    preprints = []

    review = []

    current_year = datetime.now(timezone.utc).year

    included_count = 0

    # --------------------------------------------------
    # 4. Filter papers by author affiliation
    # --------------------------------------------------

    for cluster in clusters:

        representative = best_record(
            cluster["records"]
        )

        included, reason, affiliation = (
            check_affiliation(
                cluster,
                metadata
            )
        )

        if not included:

            review.append({
                "Year": representative["Year"],
                "Title": representative["Title"],
                "Reason": reason,
                "ADS affiliation": affiliation,
                "DOI URL": representative["DOI URL"],
                "ADS URL": representative["ADS URL"]
            })

            continue

        row = output_row(
            cluster,
            metadata,
            order
        )

        # Prefer published version over preprint.
        if representative["preprint"]:

            if int(representative["Year"]) >= (
                current_year - 1
            ):
                preprints.append(row)

        else:

            # A missing journal can indicate incomplete
            # publication metadata. Do not count it as
            # a verified published article automatically.

            if not plain(
                representative["Journal"]
            ):

                review.append({
                    "Year": representative["Year"],
                    "Title": representative["Title"],
                    "Reason": "Missing journal metadata",
                    "ADS affiliation": affiliation,
                    "DOI URL": representative["DOI URL"],
                    "ADS URL": representative["ADS URL"]
                })

                continue

            annual[
                representative["Year"]
            ].append(row)

        included_count += 1

    # --------------------------------------------------
    # 5. Create output directory
    # --------------------------------------------------

    output_dir.mkdir(
        parents=True,
        exist_ok=True
    )

    # --------------------------------------------------
    # 6. Generate annual CSV files
    #
    # IMPORTANT: No individual yearly summary rows.
    # --------------------------------------------------

    years = set(annual.keys())

    # Regenerate existing years, including years
    # where filtering leaves zero qualifying papers.
    # This avoids leaving stale unfiltered rows
    # when the live mode is eventually enabled.

    for old_file in LIVE_OUTPUT.glob(
        "publications_*.csv"
    ):

        match = re.fullmatch(
            r"publications_(\d{4})\.csv",
            old_file.name
        )

        if match:
            years.add(match.group(1))

    # Always generate the years used for the
    # institute's 2019-present statistics.

    years.update(
        str(year)
        for year in range(
            START_YEAR,
            current_year + 1
        )
    )

    for year in sorted(
        years,
        reverse=True
    ):

        rows = annual.get(year, [])

        rows.sort(
            key=lambda row: row["Title"].casefold()
        )

        file = (
            output_dir
            / f"publications_{year}.csv"
        )

        write_csv(
            file,
            rows
        )

        print(
            f"{year}: "
            f"{len(rows)} affiliation-verified "
            "published papers"
        )

    # --------------------------------------------------
    # 7. Generate recent preprints
    # --------------------------------------------------

    preprints.sort(
        key=lambda row: row["Title"].casefold()
    )

    write_csv(
        output_dir / "recent_preprints.csv",
        preprints
    )

    # --------------------------------------------------
    # 8. Generate overall statistics
    # --------------------------------------------------

    number_of_papers = create_summary(
        output_dir,
        annual
    )

    # --------------------------------------------------
    # 9. Generate affiliation review report
    # --------------------------------------------------

    write_review_report(
        output_dir,
        review
    )

    # --------------------------------------------------
    # 10. Safety check before live publishing
    # --------------------------------------------------

    if (
        OUTPUT_MODE == "live"
        and number_of_papers == 0
    ):
        raise RuntimeError(
            "No affiliation-verified published papers "
            "were found for 2019-present. "
            "Live publication update stopped."
        )

    print()
    print("=" * 60)
    print("IMAC UPDATE COMPLETE")
    print("=" * 60)

    print(
        f"Total unique works examined: {len(clusters)}"
    )

    print(
        f"Affiliation-eligible works processed: "
        f"{included_count}"
    )

    print(
        f"Works excluded or requiring review: "
        f"{len(review)}"
    )

    print(
        f"Recent preprints: {len(preprints)}"
    )

    print(
        f"Output directory: {output_dir}"
    )


if __name__ == "__main__":
    main()
