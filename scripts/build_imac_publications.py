"""Build IMAC-wide publications from researcher CSVs.

Affiliation evidence:
    NASA ADS -> arXiv author metadata -> paper PDF.

This version:
    - Focuses on publications from 2019 onward.
    - Checks arXiv:2507.16707 first.
    - Performs up to 30 new verification checks per run.
    - Saves verification results in a cache.
    - Creates affiliation audit and review reports.
    - Generates overall IMAC publication statistics.
    - Uses preview mode by default.

Individual researcher CSV files are not modified.
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


# ============================================================
# CONFIGURATION
# ============================================================

ROOT = Path(__file__).resolve().parent.parent

SOURCE = ROOT / "docs" / "publications"

LIVE_OUTPUT = ROOT / "docs" / "imac"

PREVIEW_OUTPUT = ROOT / "docs" / "imac_affiliation_preview"

CONFIG = ROOT / "researchers.json"

CACHE_FILE = PREVIEW_OUTPUT / "affiliation_cache.json"

ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"

ARXIV_API = "https://export.arxiv.org/api/query"

START_YEAR = 2019

# Keep preview mode until we verify the results.
MODE = os.environ.get(
    "IMAC_OUTPUT_MODE",
    "preview"
).strip().lower()

# Maximum new affiliation verification attempts per run.
MAX_NEW_CHECKS = int(
    os.environ.get("IMAC_MAX_NEW_CHECKS", "30")
)

# Test this publication first:
# Simulating realistic Lyman-alpha emitting galaxies
# including the effect of radiative transfer.
PRIORITY_ARXIV = "2507.16707"

MAX_PDF_BYTES = 16 * 1024 * 1024

FIELDS = [
    "Title",
    "Authors",
    "Journal",
    "Citation (ADS)",
    "DOI URL",
    "ADS URL"
]

USER_AGENT = (
    "IMAC-Publications/1.1 "
    "(research publication metadata updater)"
)


# ============================================================
# AFFILIATION MATCHING
# ============================================================

# Recognize IMAC and Missouri S&T.
# Never match the abbreviation "S&T" alone.

AFF_PATTERNS = [
    re.compile(
        r"\bMissouri\s+University\s+of\s+Science\s*"
        r"(?:and|&)\s*Technology\b",
        re.I
    ),

    re.compile(
        r"\bMissouri\s+S\s*(?:&|and)\s*T\b",
        re.I
    ),

    re.compile(
        r"\bInstitute\s+for\s+Multi[\s-]*messenger\s+"
        r"Astrophysics\s*(?:and|&)\s*Cosmology\b",
        re.I
    ),
]

ARXIV_ID = re.compile(
    r"(?i)(?:arxiv(?:\.org/(?:abs|pdf)/|[:./\s])|"
    r"10\.48550/arxiv\.)"
    r"(\d{4}\.\d{4,5})(?:v\d+)?"
)

ARXIV_BIB = re.compile(
    r"\d{4}arXiv(\d{4})(\d{4,5})",
    re.I
)

ATOM = "{http://www.w3.org/2005/Atom}"

ARXIV_NS = "{http://arxiv.org/schemas/atom}"

LAST_ARXIV_REQUEST = 0.0


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

    text = text.replace(
        "α",
        "alpha"
    ).replace(
        r"\alpha",
        "alpha"
    )

    return re.sub(
        r"[^a-z0-9]",
        "",
        text
    )


def doi_key(value):

    value = re.sub(
        r"^https?://(?:dx\.)?doi\.org/",
        "",
        plain(value),
        flags=re.I
    )

    return unquote(
        re.sub(
            r"^doi:\s*",
            "",
            value,
            flags=re.I
        )
    ).casefold()


def bibcode_from_url(value):

    match = re.search(
        r"/abs/([^/?#]+)",
        plain(value)
    )

    return (
        unquote(match.group(1))
        if match
        else ""
    )


def is_preprint(row):

    return (
        "arxiv" in row["Journal"].casefold()
        or row["doi_key"].startswith(
            "10.48550/arxiv."
        )
        or plain(row["Title"]).casefold().startswith(
            "arxiv:"
        )
    )


# ============================================================
# READ INDIVIDUAL RESEARCHER PUBLICATION FILES
# ============================================================

def read_records():

    researchers = json.loads(
        CONFIG.read_text(
            encoding="utf-8"
        )
    )["researchers"]

    if not researchers:
        raise RuntimeError(
            "No researchers found in researchers.json"
        )

    records = []

    for person in researchers:

        path = SOURCE / (
            person["orcid"] + ".csv"
        )

        if not path.exists():
            raise FileNotFoundError(
                f"Missing individual publication file: {path}"
            )

        with path.open(
            encoding="utf-8-sig",
            newline=""
        ) as stream:

            reader = csv.DictReader(stream)

            required = {
                "Year",
                "Title",
                "Journal",
                "DOI URL",
                "ADS URL"
            }

            if not required.issubset(
                reader.fieldnames or []
            ):
                raise ValueError(
                    f"Unexpected columns in {path}"
                )

            if not (
                {"Citation (ADS)", "Citations"}
                & set(reader.fieldnames or [])
            ):
                raise ValueError(
                    f"Missing ADS citation column in {path}"
                )

            for row in reader:

                year = plain(
                    row.get("Year")
                )

                title = plain(
                    row.get("Title")
                )

                if not (
                    len(year) == 4
                    and year.isdigit()
                    and title
                ):
                    continue

                citation = row.get(
                    "Citation (ADS)"
                )

                if (
                    citation is None
                    or not str(citation).strip()
                ):
                    citation = row.get(
                        "Citations",
                        ""
                    )

                row.update({
                    "Year": year,

                    "Title": title,

                    "Journal": plain(
                        row.get("Journal")
                    ),

                    "Citation (ADS)": str(
                        citation or ""
                    ).strip(),

                    "researcher": person["name"],

                    "doi_key": doi_key(
                        row.get("DOI URL", "")
                    ),

                    "bibcode": bibcode_from_url(
                        row.get("ADS URL", "")
                    ),

                    "title_key": title_key(title),
                })

                row["preprint"] = is_preprint(row)

                records.append(row)

    if not records:
        raise RuntimeError(
            "No publications found in the researcher CSVs"
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

        other_key = other["title_key"]

        if abs(
            int(row["Year"])
            - int(other["Year"])
        ) > 2:
            continue

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

        cluster = next(
            (
                item
                for item in clusters
                if same_paper(row, item)
            ),
            None
        )

        if cluster is None:

            cluster = {
                "records": [],
                "researchers": set(),
                "dois": set(),
                "bibcodes": set()
            }

            clusters.append(cluster)

        cluster["records"].append(row)

        cluster["researchers"].add(
            row["researcher"]
        )

        if row["doi_key"]:
            cluster["dois"].add(
                row["doi_key"]
            )

        if row["bibcode"]:
            cluster["bibcodes"].add(
                row["bibcode"]
            )

    return clusters


# ============================================================
# PREFER PUBLISHED PAPERS OVER PREPRINTS
# ============================================================

def best_record(records):

    def rank(row):

        value = row["Citation (ADS)"]

        return (
            not row["preprint"],
            bool(row["Journal"]),
            bool(row["doi_key"]),
            bool(row["bibcode"]),
            int(value)
            if value.isdigit()
            else -1
        )

    return max(
        records,
        key=rank
    )


# ============================================================
# RECOGNIZE PRIORITY PAPER
# ============================================================

def is_priority_paper(cluster):

    """
    Identify the 2025 test paper even if ORCID or ADS
    does not contain its arXiv identifier.
    """

    for row in cluster["records"]:

        identifiers = " ".join([
            str(row.get("DOI URL", "")),
            str(row.get("ADS URL", "")),
            str(row.get("Title", "")),
            str(row.get("Journal", ""))
        ])

        title = row["title_key"]

        if PRIORITY_ARXIV in identifiers:
            return True

        if (
            "simulatingrealistic" in title
            and "radiativetransfer" in title
            and "lyman" in title
        ):
            return True

    return False


# ============================================================
# RETRIEVE NASA ADS METADATA
# ============================================================

def fetch_ads(records, token):

    lookups = sorted({
        ("bibcode", row["bibcode"])
        for row in records
        if row["bibcode"]
    })

    lookups += sorted({
        ("doi", row["doi_key"])
        for row in records
        if row["doi_key"]
    })

    by_bibcode = {}
    by_doi = {}

    for start in range(
        0,
        len(lookups),
        15
    ):

        batch = lookups[
            start:start + 15
        ]

        clauses = []

        for kind, value in batch:

            safe = (
                value.replace("\\", "\\\\")
                .replace('"', '\\"')
            )

            clauses.append(
                f'{kind}:"{safe}"'
            )

        url = ADS_API + "?" + urlencode({
            "q": " OR ".join(clauses),

            "fl": (
                "bibcode,doi,identifier,"
                "first_author,author_count,"
                "aff,citation_count"
            ),

            "rows": 200,
        })

        request = Request(
            url,
            headers={
                "Authorization": f"Bearer {token}",
                "Accept": "application/json",
                "User-Agent": USER_AGENT
            }
        )

        try:

            with urlopen(
                request,
                timeout=75
            ) as reply:

                result = json.load(reply)

        except HTTPError as exc:

            raise RuntimeError(
                "ADS metadata request failed "
                f"(HTTP {exc.code})"
            ) from None

        except (URLError, TimeoutError) as exc:

            raise RuntimeError(
                "ADS metadata request failed: "
                f"{type(exc).__name__}"
            ) from None

        response = result.get(
            "response",
            {}
        )

        documents = response.get("docs")

        if (
            not isinstance(documents, list)
            or response.get("numFound", 0) > len(documents)
        ):
            raise RuntimeError(
                "Incomplete ADS metadata response; "
                "refusing to update publication files"
            )

        for document in documents:

            if document.get("bibcode"):

                by_bibcode[
                    document["bibcode"]
                ] = document

            dois = document.get("doi") or []

            if isinstance(dois, str):
                dois = [dois]

            for doi in dois:

                by_doi[
                    doi_key(doi)
                ] = document

    return by_bibcode, by_doi


# ============================================================
# FIND ADS DOCUMENTS FOR A PUBLICATION
# ============================================================

def documents_for(cluster, metadata):

    bibcodes, dois = metadata

    seen = set()
    documents = []

    for row in cluster["records"]:

        candidates = (
            bibcodes.get(row["bibcode"]),
            dois.get(row["doi_key"])
        )

        for document in candidates:

            if not document:
                continue

            key = (
                document.get("bibcode")
                or id(document)
            )

            if key not in seen:

                seen.add(key)
                documents.append(document)

    return documents


# ============================================================
# NORMALIZE AFFILIATION TEXT
# ============================================================

def normalize_affiliation(text):

    text = plain(text)

    text = re.sub(
        r"(?<=\w)-\s*\n\s*(?=\w)",
        "-",
        text
    )

    return re.sub(
        r"\s+",
        " ",
        text
    )


def affiliation_match(text):

    normalized = normalize_affiliation(text)

    return any(
        pattern.search(normalized)
        for pattern in AFF_PATTERNS
    )


# ============================================================
# CHECK NASA ADS AFFILIATIONS
# ============================================================

def ads_affiliation(documents):

    found_any = False

    for document in documents:

        affiliations = document.get(
            "aff"
        ) or []

        if isinstance(
            affiliations,
            str
        ):
            affiliations = [affiliations]

        for item in affiliations:

            value = normalize_affiliation(item)

            if value.casefold() in {
                "",
                "-",
                "n/a",
                "none",
                "unknown",
                "not available"
            }:
                continue

            found_any = True

            if affiliation_match(value):

                return (
                    True,
                    value[:350],
                    "ADS"
                )

    if found_any:

        return (
            False,
            "ADS affiliations did not establish "
            "IMAC / Missouri S&T",
            "ADS"
        )

    return (
        False,
        "ADS affiliations unavailable",
        "ADS"
    )


# ============================================================
# IDENTIFY ARXIV PAPER
# ============================================================

def arxiv_id_for(cluster, documents):

    # For the priority paper, use the known arXiv ID.
    # Its journal DOI may not contain this identifier.
    if is_priority_paper(cluster):
        return PRIORITY_ARXIV

    pieces = []

    for row in cluster["records"]:

        pieces.extend([
            row.get("DOI URL", ""),
            row.get("ADS URL", ""),
            row.get("Title", ""),
            row.get("Journal", "")
        ])

    for document in documents:

        identifiers = document.get(
            "identifier"
        ) or []

        if isinstance(
            identifiers,
            str
        ):
            identifiers = [identifiers]

        pieces.extend(
            identifiers
            + [document.get("bibcode", "")]
        )

    for piece in pieces:

        match = ARXIV_ID.search(
            str(piece)
        )

        if match:
            return match.group(1)

        match = ARXIV_BIB.search(
            str(piece)
        )

        if match:

            return (
                match.group(1)
                + "."
                + match.group(2)
            )

    return ""


# ============================================================
# RESPECT ARXIV REQUEST SPACING
# ============================================================

def wait_for_arxiv():

    global LAST_ARXIV_REQUEST

    delta = (
        time.monotonic()
        - LAST_ARXIV_REQUEST
    )

    if (
        LAST_ARXIV_REQUEST
        and delta < 3.1
    ):

        time.sleep(
            3.1 - delta
        )

    LAST_ARXIV_REQUEST = time.monotonic()


# ============================================================
# CHECK ARXIV AUTHOR AFFILIATION METADATA
# ============================================================

def arxiv_author_affiliation(identifier):

    wait_for_arxiv()

    url = ARXIV_API + "?" + urlencode({
        "id_list": identifier,
        "max_results": 1
    })

    request = Request(
        url,
        headers={
            "User-Agent": USER_AGENT
        }
    )

    with urlopen(
        request,
        timeout=35
    ) as reply:

        raw = reply.read(512_000)

    root = ET.fromstring(raw)

    for entry in root.findall(
        ATOM + "entry"
    ):

        for author in entry.findall(
            ATOM + "author"
        ):

            for affiliation in author.findall(
                ARXIV_NS + "affiliation"
            ):

                if (
                    affiliation.text
                    and affiliation_match(
                        affiliation.text
                    )
                ):

                    return normalize_affiliation(
                        affiliation.text
                    )[:350]

    return ""


# ============================================================
# FIND AN OPEN-ACCESS PUBLISHER PDF
# ============================================================

def openalex_pdf_url(cluster):

    """
    Try to find an open-access PDF when an arXiv ID
    is not available.
    """

    representative = best_record(
        cluster["records"]
    )

    doi = representative["doi_key"]

    if (
        not doi
        or doi.startswith(
            "10.48550/arxiv."
        )
    ):
        return ""

    url = (
        "https://api.openalex.org/works/"
        "https://doi.org/"
        + quote(doi, safe="/")
    )

    request = Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "application/json"
        }
    )

    with urlopen(
        request,
        timeout=25
    ) as reply:

        obj = json.load(reply)

    locations = (
        [obj.get("best_oa_location") or {}]
        + (obj.get("locations") or [])
    )

    for location in locations:

        value = location.get(
            "pdf_url"
        ) or ""

        parts = urlsplit(value)

        if (
            parts.scheme == "https"
            and parts.hostname
            and parts.hostname not in {
                "localhost"
            }
        ):
            return value

    return ""


# ============================================================
# READ AFFILIATION FROM PAPER PDF
# ============================================================

def pdf_affiliation(pdf_url):

    """
    Search the first-page author/title area.

    Do not use the complete paper text, because
    acknowledgments and references could produce
    false affiliation matches.
    """

    parts = urlsplit(pdf_url)

    if (
        parts.scheme != "https"
        or not parts.hostname
    ):

        return (
            "",
            "Invalid PDF URL"
        )

    if parts.hostname in {
        "localhost",
        "127.0.0.1",
        "169.254.169.254"
    }:

        return (
            "",
            "Unsafe PDF URL"
        )

    if parts.hostname.endswith(
        "arxiv.org"
    ):
        wait_for_arxiv()

    request = Request(
        pdf_url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "application/pdf"
        }
    )

    with urlopen(
        request,
        timeout=50
    ) as reply:

        pdf_bytes = reply.read(
            MAX_PDF_BYTES + 1
        )

    if len(pdf_bytes) > MAX_PDF_BYTES:

        return (
            "",
            "PDF exceeds configured download limit"
        )

    if not pdf_bytes.lstrip().startswith(
        b"%PDF"
    ):

        return (
            "",
            "Source did not serve a PDF"
        )

    with pymupdf.open(
        stream=pdf_bytes,
        filetype="pdf"
    ) as document:

        for page_number in range(
            min(len(document), 2)
        ):

            text = document[
                page_number
            ].get_text(
                "text",
                sort=True
            )

            if page_number == 0:

                match = re.search(
                    r"\b(?:ABSTRACT|INTRODUCTION)\b",
                    text,
                    flags=re.I
                )

                candidate = (
                    text[:match.start()]
                    if match
                    else text[:8500]
                )

            else:

                # Only consider the second page when it
                # explicitly starts with author affiliations.

                if not re.search(
                    r"(?i)affiliations?\s*"
                    r"(?:of\s+authors)?",
                    text[:700]
                ):
                    continue

                candidate = text[:4500]

            if affiliation_match(candidate):

                cleaned = normalize_affiliation(
                    candidate
                )

                match = next(
                    (
                        pattern.search(cleaned)
                        for pattern in AFF_PATTERNS
                        if pattern.search(cleaned)
                    ),
                    None
                )

                if match:

                    evidence = cleaned[
                        max(
                            0,
                            match.start() - 65
                        ):
                        match.end() + 100
                    ][:350]

                else:

                    evidence = cleaned[:350]

                return (
                    evidence,
                    f"PDF page {page_number + 1}"
                )

    return (
        "",
        "No confirmed affiliation "
        "in inspected PDF header"
    )


# ============================================================
# CACHE AFFILIATION RESULTS
# ============================================================

def cache_key(cluster, arxiv_id):

    publication = best_record(
        cluster["records"]
    )

    if publication["doi_key"]:

        return (
            "doi:"
            + publication["doi_key"]
        )

    if arxiv_id:

        return (
            "arxiv:"
            + arxiv_id
        )

    if publication["bibcode"]:

        return (
            "ads:"
            + publication["bibcode"]
        )

    return (
        "title:"
        + publication["title_key"]
    )


def load_cache():

    if not CACHE_FILE.exists():
        return {}

    data = json.loads(
        CACHE_FILE.read_text(
            encoding="utf-8"
        )
    )

    return (
        data
        if isinstance(data, dict)
        else {}
    )


def save_cache(cache):

    CACHE_FILE.parent.mkdir(
        parents=True,
        exist_ok=True
    )

    temporary = CACHE_FILE.with_suffix(
        ".json.tmp"
    )

    temporary.write_text(
        json.dumps(
            cache,
            indent=2,
            sort_keys=True
        ),
        encoding="utf-8"
    )

    os.replace(
        temporary,
        CACHE_FILE
    )


# ============================================================
# COMBINED AFFILIATION VERIFICATION
#
# 1. NASA ADS
# 2. arXiv metadata
# 3. PDF author-affiliation block
# ============================================================

def verify_affiliation(
    cluster,
    metadata,
    cache,
    checks
):

    documents = documents_for(
        cluster,
        metadata
    )

    found, evidence, source = ads_affiliation(
        documents
    )

    if found:

        return (
            "verified",
            source,
            evidence,
            ""
        )

    arxiv_id = arxiv_id_for(
        cluster,
        documents
    )

    key = cache_key(
        cluster,
        arxiv_id
    )

    old = cache.get(key)

    if old:

        age = (
            datetime.now(timezone.utc)
            - datetime.fromisoformat(
                old["checked_at"]
            )
        ).days

        days = (
            3
            if old.get("status") == "error"
            else 30
        )

        # Successfully verified affiliations remain cached.
        # Unverified results are checked periodically.

        if (
            old.get("status") == "verified"
            or age < days
        ):

            return (
                old["status"],
                old.get(
                    "source",
                    "cache"
                ),
                old.get(
                    "evidence",
                    ""
                ),
                arxiv_id
            )

    if checks["used"] >= MAX_NEW_CHECKS:

        return (
            "pending",
            "budget",
            "Pending affiliation check "
            "on a later run",
            arxiv_id
        )

    checks["used"] += 1

    status = "unverified"

    method = "none"

    detail = (
        "No accessible, confirmed affiliation"
    )

    errors = []

    # --------------------------------------------------------
    # First fallback: arXiv author affiliation metadata
    # --------------------------------------------------------

    if arxiv_id:

        try:

            evidence = arxiv_author_affiliation(
                arxiv_id
            )

            if evidence:

                status = "verified"

                method = "arXiv author metadata"

                detail = evidence

        except (
            HTTPError,
            URLError,
            TimeoutError,
            ET.ParseError,
            ValueError
        ) as exc:

            errors.append(
                "arXiv metadata: "
                + type(exc).__name__
            )

    # --------------------------------------------------------
    # Second fallback: paper PDF
    # --------------------------------------------------------

    if status != "verified":

        pdf_url = (
            "https://arxiv.org/pdf/"
            + arxiv_id
            if arxiv_id
            else ""
        )

        if not pdf_url:

            try:

                pdf_url = openalex_pdf_url(
                    cluster
                )

            except (
                HTTPError,
                URLError,
                TimeoutError,
                ValueError
            ) as exc:

                errors.append(
                    "OpenAlex: "
                    + type(exc).__name__
                )

        if pdf_url:

            try:

                evidence, detail = pdf_affiliation(
                    pdf_url
                )

                if evidence:

                    status = "verified"

                    method = "PDF header"

                    detail = evidence

                else:

                    method = "PDF checked"

            except (
                HTTPError,
                URLError,
                TimeoutError,
                RuntimeError,
                ValueError
            ) as exc:

                errors.append(
                    "PDF: "
                    + type(exc).__name__
                )

    if (
        status != "verified"
        and errors
    ):

        status = "error"

        detail = "; ".join(
            errors
        )[:350]

    cache[key] = {
        "status": status,

        "source": method,

        "evidence": detail[:350],

        "checked_at": datetime.now(
            timezone.utc
        ).isoformat(),

        "arxiv_id": arxiv_id,
    }

    return (
        status,
        method,
        detail,
        arxiv_id
    )


# ============================================================
# FORMAT AUTHORS
# ============================================================

def author_label(
    cluster,
    documents,
    order
):

    names = sorted(
        cluster["researchers"],
        key=lambda name: order.get(
            name,
            9999
        )
    )

    included = ", ".join(
        (
            name.split()[0][0]
            + ". "
            + name.split()[-1]
        )
        if len(name.split()) > 1
        else name
        for name in names
    )

    for document in documents:

        first = document.get(
            "first_author"
        ) or ""

        if isinstance(first, list):

            first = (
                first[0]
                if first
                else ""
            )

        if first:

            surname = plain(
                first
            ).split(",")[0]

            try:

                multiple = (
                    int(
                        document.get(
                            "author_count"
                        ) or 2
                    ) > 1
                )

            except (
                TypeError,
                ValueError
            ):

                multiple = True

            return (
                f"{surname}"
                f"{' et al.' if multiple else ''}"
                f" (incl. {included})"
            )

    return (
        f"IMAC contributors: {included}"
    )


# ============================================================
# FORMAT PUBLICATION ROW
# ============================================================

def output_row(
    cluster,
    metadata,
    order
):

    chosen = best_record(
        cluster["records"]
    )

    documents = documents_for(
        cluster,
        metadata
    )

    # Avoid counting both journal and arXiv citations
    # independently for the same publication.

    counts = [
        int(row["Citation (ADS)"])
        for row in cluster["records"]
        if row["Citation (ADS)"].isdigit()
    ]

    counts += [
        int(document["citation_count"])
        for document in documents
        if str(
            document.get(
                "citation_count",
                ""
            )
        ).isdigit()
    ]

    citation = (
        max(counts)
        if counts
        else ""
    )

    return {
        "Title": html.escape(
            plain(chosen["Title"]),
            quote=False
        ),

        "Authors": html.escape(
            author_label(
                cluster,
                documents,
                order
            ),
            quote=False
        ),

        "Journal": html.escape(
            plain(chosen["Journal"]),
            quote=False
        ),

        "Citation (ADS)": citation,

        "DOI URL": chosen["DOI URL"],

        "ADS URL": chosen["ADS URL"],
    }


# ============================================================
# WRITE CSV FILES
# ============================================================

def write_csv(
    path,
    rows,
    fields=FIELDS
):

    temporary = path.with_suffix(
        ".csv.tmp"
    )

    with temporary.open(
        "w",
        newline="",
        encoding="utf-8"
    ) as stream:

        writer = csv.DictWriter(
            stream,
            fieldnames=fields
        )

        writer.writeheader()

        writer.writerows(rows)

    os.replace(
        temporary,
        path
    )


# ============================================================
# OVERALL IMAC PUBLICATION STATISTICS
# ============================================================

def write_summary(
    output_dir,
    annual
):

    year_now = datetime.now(
        timezone.utc
    ).year

    eligible = [
        paper
        for year, papers in annual.items()
        if START_YEAR <= int(year) <= year_now
        for paper in papers
    ]

    citations = [
        int(
            str(row["Citation (ADS)"])
        )
        for row in eligible
        if str(
            row["Citation (ADS)"]
        ).isdigit()
    ]

    count = len(eligible)

    total = sum(citations)

    covered = len(citations)

    # --------------------------------------------------------
    # Summary sentence requested by Shun
    # --------------------------------------------------------

    article_label = (
        "article"
        if count == 1
        else "articles"
    )

    statement = (
        f"IMAC published a total of "
        f"{count:,} {article_label}, "
        f"cited a total of "
        f"{total:,} times "
        f"(according to NASA ADS)."
    )

    note = (
        f"2019–{year_now}; "
        f"affiliation-verified publications. "
        f"ADS citation counts available for "
        f"{covered}/{count} articles. "
        "Counts are cumulative to the latest "
        "available update."
    )

    # --------------------------------------------------------
    # CSV summary
    # --------------------------------------------------------

    with (
        output_dir / "summary_statistics.csv"
    ).open(
        "w",
        newline="",
        encoding="utf-8"
    ) as stream:

        writer = csv.writer(stream)

        writer.writerow([
            "IMAC Publication Summary"
        ])

        writer.writerow([
            statement
        ])

    # --------------------------------------------------------
    # JSON summary
    # --------------------------------------------------------

    (
        output_dir / "summary.json"
    ).write_text(
        json.dumps(
            {
                "start_year": START_YEAR,

                "end_year": year_now,

                "published_articles": count,

                "ads_citations": total,

                "papers_with_ads_data": covered,

                "summary": statement,

                "note": note,
            },
            indent=2
        ),
        encoding="utf-8"
    )

    # --------------------------------------------------------
    # HTML summary for possible Terminalfour embedding
    # --------------------------------------------------------

    (
        output_dir / "summary.html"
    ).write_text(
        "<!doctype html>"
        "<html lang='en'>"
        "<head>"
        "<meta charset='utf-8'>"
        "<meta name='viewport' "
        "content='width=device-width,initial-scale=1'>"
        "<style>"
        "body{font-family:Arial,sans-serif;"
        "color:#003c4a;margin:10px;"
        "text-align:center}"
        "p{font-size:20px;font-weight:600;"
        "line-height:1.5}"
        "small{font-size:12px;color:#555}"
        "</style>"
        "</head>"
        "<body>"
        f"<p>{html.escape(statement)}</p>"
        f"<small>{html.escape(note)}</small>"
        "</body>"
        "</html>",
        encoding="utf-8"
    )

    print(statement)
    print(note)

    return count


# ============================================================
# MAIN PROGRAM
# ============================================================

def main():

    token = os.environ.get(
        "ADS_API_TOKEN"
    )

    if not token:
        raise RuntimeError(
            "Missing ADS_API_TOKEN secret"
        )

    if MODE not in {
        "preview",
        "live"
    }:
        raise ValueError(
            "IMAC_OUTPUT_MODE must be preview or live"
        )

    output = (
        PREVIEW_OUTPUT
        if MODE == "preview"
        else LIVE_OUTPUT
    )

    # --------------------------------------------------------
    # Step 1: Read researcher publications
    # --------------------------------------------------------

    researchers, records = read_records()

    # --------------------------------------------------------
    # Step 2: Remove duplicates
    # --------------------------------------------------------

    clusters = collapse(records)

    year_now = datetime.now(
        timezone.utc
    ).year

    # --------------------------------------------------------
    # Step 2b: Focus on 2019-present
    # --------------------------------------------------------

    all_clusters_count = len(clusters)

    clusters = [
        cluster
        for cluster in clusters
        if (
            START_YEAR
            <= int(
                best_record(
                    cluster["records"]
                )["Year"]
            )
            <= year_now
        )
    ]

    recent_records = [
        record
        for cluster in clusters
        for record in cluster["records"]
    ]

    print(
        f"Total unique publications: "
        f"{all_clusters_count}"
    )

    print(
        f"Publications from "
        f"{START_YEAR}-{year_now}: "
        f"{len(clusters)}"
    )

    # --------------------------------------------------------
    # Step 3: Retrieve ADS metadata
    # Only for publications from 2019 onward
    # --------------------------------------------------------

    metadata = fetch_ads(
        recent_records,
        token
    )

    order = {
        person["name"]: index
        for index, person in enumerate(
            researchers
        )
    }

    cache = load_cache()

    checks = {
        "used": 0
    }

    annual = defaultdict(list)

    preprints = []

    audit = []

    statuses = Counter()

    # --------------------------------------------------------
    # Step 4: Set verification priority
    #
    # 1. arXiv:2507.16707
    # 2. Remaining papers, newest to oldest
    # --------------------------------------------------------

    clusters.sort(
        key=lambda cluster: (
            1 if is_priority_paper(cluster) else 0,
            int(
                best_record(
                    cluster["records"]
                )["Year"]
            )
        ),
        reverse=True
    )

    priority_found = any(
        is_priority_paper(cluster)
        for cluster in clusters
    )

    print(
        "Priority paper "
        f"arXiv:{PRIORITY_ARXIV} found: "
        f"{priority_found}"
    )

    # --------------------------------------------------------
    # Step 5: Verify affiliations
    # --------------------------------------------------------

    for cluster in clusters:

        chosen = best_record(
            cluster["records"]
        )

        # Force retry if the priority paper was previously
        # cached as unverified or error.
        # Keep any positive verification.

        if is_priority_paper(cluster):

            documents = documents_for(
                cluster,
                metadata
            )

            arxiv_id = arxiv_id_for(
                cluster,
                documents
            )

            key = cache_key(
                cluster,
                arxiv_id
            )

            if (
                key in cache
                and cache[key].get("status") != "verified"
            ):
                del cache[key]

        status, source, evidence, arxiv_id = (
            verify_affiliation(
                cluster,
                metadata,
                cache,
                checks
            )
        )

        statuses[status] += 1

        # Print a clearly identifiable test result
        # in the GitHub Actions logs.

        if is_priority_paper(cluster):

            print("=" * 60)

            print(
                "PRIORITY PAPER TEST RESULT"
            )

            print(
                f"Paper: arXiv:{PRIORITY_ARXIV}"
            )

            print(
                f"Status: {status}"
            )

            print(
                f"Verification source: {source}"
            )

            print(
                f"Evidence: {evidence}"
            )

            print(
                f"Detected arXiv ID: "
                f"{arxiv_id or PRIORITY_ARXIV}"
            )

            print("=" * 60)

        audit.append({
            "Year": chosen["Year"],

            "Title": chosen["Title"],

            "Status": status,

            "Source": source,

            "Evidence": evidence,

            "arXiv": arxiv_id,

            "DOI URL": chosen["DOI URL"],

            "ADS URL": chosen["ADS URL"],
        })

        if status != "verified":
            continue

        row = output_row(
            cluster,
            metadata,
            order
        )

        # ----------------------------------------------------
        # Separate preprints and published articles
        # ----------------------------------------------------

        if chosen["preprint"]:

            if int(
                chosen["Year"]
            ) >= year_now - 1:

                preprints.append(row)

        else:

            if chosen["Journal"]:

                annual[
                    chosen["Year"]
                ].append(row)

    # --------------------------------------------------------
    # Step 6: Create output folder
    # --------------------------------------------------------

    output.mkdir(
        parents=True,
        exist_ok=True
    )

    # Save affiliation verification results.
    save_cache(cache)

    # --------------------------------------------------------
    # Step 7: Generate yearly publication tables
    #
    # NO yearly summary rows.
    # --------------------------------------------------------

    years = set(annual)

    # Preserve existing yearly filenames only
    # for 2019 onward.

    for old_file in LIVE_OUTPUT.glob(
        "publications_*.csv"
    ):

        match = re.fullmatch(
            r"publications_(\d{4})\.csv",
            old_file.name
        )

        if match:

            year = int(
                match.group(1)
            )

            if START_YEAR <= year <= year_now:

                years.add(
                    str(year)
                )

    years.update(
        str(year)
        for year in range(
            START_YEAR,
            year_now + 1
        )
    )

    for year in sorted(
        years,
        reverse=True
    ):

        rows = sorted(
            annual.get(
                year,
                []
            ),
            key=lambda row: row[
                "Title"
            ].casefold()
        )

        write_csv(
            output / f"publications_{year}.csv",
            rows
        )

        print(
            f"{year}: {len(rows)} "
            "affiliation-verified published papers"
        )

    # --------------------------------------------------------
    # Step 8: Generate recent preprints
    # --------------------------------------------------------

    write_csv(
        output / "recent_preprints.csv",
        sorted(
            preprints,
            key=lambda row: row[
                "Title"
            ].casefold()
        )
    )

    # --------------------------------------------------------
    # Step 9: Generate overall IMAC statistics
    # --------------------------------------------------------

    number_of_papers = write_summary(
        output,
        annual
    )

    # --------------------------------------------------------
    # Step 10: Generate affiliation audit and review reports
    # --------------------------------------------------------

    fields = [
        "Year",
        "Title",
        "Status",
        "Source",
        "Evidence",
        "arXiv",
        "DOI URL",
        "ADS URL"
    ]

    write_csv(
        output / "affiliation_audit.csv",
        audit,
        fields
    )

    write_csv(
        output / "affiliation_review.csv",
        [
            row
            for row in audit
            if row["Status"] != "verified"
        ],
        fields
    )

    # --------------------------------------------------------
    # Step 11: Print final summary
    # --------------------------------------------------------

    print(
        "Verification status:",
        dict(statuses)
    )

    print(
        f"New arXiv/PDF checks this run: "
        f"{checks['used']} / {MAX_NEW_CHECKS}"
    )

    print(
        f"Output mode: {MODE}"
    )

    print(
        f"Files saved in: {output}"
    )

    # --------------------------------------------------------
    # Step 12: Safety check
    # --------------------------------------------------------

    if (
        MODE == "live"
        and (
            number_of_papers == 0
            or statuses["pending"] > 0
        )
    ):

        raise RuntimeError(
            "Live update stopped: "
            "no verified 2019+ papers, or some "
            "affiliation checks are still pending."
        )


if __name__ == "__main__":
    main()
