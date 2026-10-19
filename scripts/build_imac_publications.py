"""Build affiliation-verified IMAC publication previews from ORCID/ADS CSVs.

Evidence order: NASA ADS -> OpenAlex -> arXiv author data -> paper PDF.
Missing evidence is not evidence of a non-IMAC affiliation.

Default: write docs/imac_affiliation_preview, never overwrite live tables.
The individual researchers' career-publication CSVs are read, not modified.
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


# ============================================================
# CONFIGURATION
# ============================================================

ROOT = Path(__file__).resolve().parent.parent

SOURCE = ROOT / "docs" / "publications"

LIVE_DIR = ROOT / "docs" / "imac"

PREVIEW_DIR = ROOT / "docs" / "imac_affiliation_preview"

CACHE_FILE = PREVIEW_DIR / "affiliation_cache.json"

DECISIONS_FILE = ROOT / "affiliation_decisions.json"

RESEARCHERS_FILE = ROOT / "researchers.json"

ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"

ARXIV_API = "https://export.arxiv.org/api/query"

START_YEAR = 2019

MODE = os.getenv(
    "IMAC_OUTPUT_MODE",
    "preview"
).strip().lower()

MAX_CHECKS = int(
    os.getenv("IMAC_MAX_NEW_CHECKS", "30")
)

MAX_PDF_BYTES = 40 * 1024 * 1024

# Version 4 retries previously unresolved papers
# using the improved full-PDF affiliation checker.
CACHE_VERSION = 4

# Priority test paper.
# This is NOT an automatic inclusion override.
PRIORITY_ARXIV = "2507.16707"

USER_AGENT = (
    "IMAC-MissouriST-Publications/2.0 "
    "(institutional bibliography)"
)

CSV_COLUMNS = [
    "Title",
    "Authors",
    "Journal",
    "Citation (ADS)",
    "DOI URL",
    "ADS URL"
]

AUDIT_COLUMNS = [
    "Year",
    "Title",
    "Status",
    "Source",
    "Evidence",
    "Evidence URL",
    "arXiv",
    "DOI URL",
    "ADS URL"
]

ATOM = "{http://www.w3.org/2005/Atom}"

ARXIV_NS = "{http://arxiv.org/schemas/atom}"

LAST_ARXIV_REQUEST = 0.0


# ============================================================
# AFFILIATION MATCHING
# ============================================================

AFFILIATION_PATTERNS = [
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

ARXIV_PATTERN = re.compile(
    r"(?i)(?:arxiv(?:\.org/(?:abs|pdf)/|[:./\s])|"
    r"10\.48550/arxiv\.)"
    r"(\d{4}\.\d{4,5})(?:v\d+)?"
)

ARXIV_BIB_PATTERN = re.compile(
    r"\d{4}arXiv(\d{4})(\d{4,5})",
    re.I
)

AFFILIATION_HEADING = re.compile(
    r"(?im)^\s*(?:author\s+)?affiliations?"
    r"(?:\s+of\s+(?:the\s+)?authors)?\s*[:.]?\s*$"
)

ABSTRACT_HEADING = re.compile(
    r"(?im)^\s*(?:abstract|1\s*\.?\s*introduction)\s*$"
)

SECTION_HEADING = re.compile(
    r"(?im)^\s*(?:references|bibliography|"
    r"acknowledg(?:e)?ments?|appendix)\s*$"
)


# ============================================================
# TEXT NORMALIZATION
# ============================================================

def clean(value):

    return html.unescape(
        html.unescape(str(value or ""))
    ).strip()


def normalized_title(value):

    text = unicodedata.normalize(
        "NFKD",
        clean(value)
    ).casefold()

    text = text.replace(
        r"\alpha",
        "alpha"
    ).replace(
        "α",
        "alpha"
    )

    text = text.replace(
        r"\beta",
        "beta"
    ).replace(
        "β",
        "beta"
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
        clean(value),
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


def bibcode(value):

    match = re.search(
        r"/abs/([^/?#]+)",
        clean(value)
    )

    return (
        unquote(match.group(1))
        if match
        else ""
    )


def normalize_affiliation(text):

    text = clean(text)

    # Rejoin words split across PDF lines.
    # Example: "Technol-\nogy" -> "Technology"

    text = re.sub(
        r"(?<=[a-zA-Z])-\s*\n\s*(?=[a-zA-Z])",
        "",
        text
    )

    return re.sub(
        r"\s+",
        " ",
        text
    )


def qualifying_affiliation(text):

    text = normalize_affiliation(text)

    return any(
        pattern.search(text)
        for pattern in AFFILIATION_PATTERNS
    )


def paper_title_matches(expected, candidate):

    a = normalized_title(expected)
    b = normalized_title(candidate)

    if min(len(a), len(b)) < 24:
        return a == b

    return (
        SequenceMatcher(
            None,
            a,
            b
        ).ratio() >= 0.91
    )


def is_preprint(row):

    return (
        "arxiv" in row["Journal"].casefold()
        or row["doi_key"].startswith(
            "10.48550/arxiv."
        )
        or row["Title"].casefold().startswith(
            "arxiv:"
        )
    )


# ============================================================
# READ RESEARCHER CSV FILES
# ============================================================

def load_records():

    researchers = json.loads(
        RESEARCHERS_FILE.read_text(
            encoding="utf-8"
        )
    )["researchers"]

    records = []

    for person in researchers:

        path = (
            SOURCE / f'{person["orcid"]}.csv'
        )

        if not path.is_file():
            raise FileNotFoundError(
                f"Researcher CSV missing: {path}"
            )

        with path.open(
            newline="",
            encoding="utf-8-sig"
        ) as handle:

            reader = csv.DictReader(handle)

            cols = set(
                reader.fieldnames or []
            )

            required = {
                "Year",
                "Title",
                "Journal",
                "DOI URL",
                "ADS URL"
            }

            if not required.issubset(cols):
                raise ValueError(
                    f"Invalid CSV columns: {path}"
                )

            if not (
                {"Citation (ADS)", "Citations"} & cols
            ):
                raise ValueError(
                    f"Citation column missing: {path}"
                )

            for row in reader:

                year = clean(
                    row.get("Year")
                )

                title = clean(
                    row.get("Title")
                )

                if (
                    len(year) != 4
                    or not year.isdigit()
                    or not title
                ):
                    continue

                row.update({
                    "Year": year,

                    "Title": title,

                    "Journal": clean(
                        row.get("Journal")
                    ),

                    "Citation (ADS)": clean(
                        row.get("Citation (ADS)")
                        or row.get("Citations")
                    ),

                    "doi_key": doi_key(
                        row.get("DOI URL")
                    ),

                    "bibcode": bibcode(
                        row.get("ADS URL")
                    ),

                    "title_key": normalized_title(
                        title
                    ),

                    "researcher": person["name"],
                })

                row["preprint"] = is_preprint(row)

                records.append(row)

    if not records:
        raise RuntimeError(
            "No researcher publications were found"
        )

    return researchers, records


# ============================================================
# DEDUPLICATE PUBLICATIONS
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
            int(row["Year"])
            - int(other["Year"])
        ) > 2:
            continue

        second = other["title_key"]

        if key == second:
            return True

        if (
            len(second) >= 35
            and re.findall(r"\d+", key)
            == re.findall(r"\d+", second)
            and SequenceMatcher(
                None,
                key,
                second
            ).ratio() >= 0.985
        ):
            return True

    return False


def collapse(records):

    groups = []

    for row in records:

        group = next(
            (
                g for g in groups
                if same_paper(row, g)
            ),
            None
        )

        if group is None:

            group = {
                "records": [],
                "researchers": set(),
                "dois": set(),
                "bibcodes": set()
            }

            groups.append(group)

        group["records"].append(row)

        group["researchers"].add(
            row["researcher"]
        )

        if row["doi_key"]:
            group["dois"].add(
                row["doi_key"]
            )

        if row["bibcode"]:
            group["bibcodes"].add(
                row["bibcode"]
            )

    return groups


def preferred_record(rows):

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
        rows,
        key=rank
    )


def is_priority(group):

    return any(
        PRIORITY_ARXIV in " ".join(
            clean(row.get(key))
            for key in (
                "Title",
                "ADS URL",
                "DOI URL"
            )
        )
        or (
            "simulatingrealistic" in row["title_key"]
            and "radiativetransfer" in row["title_key"]
            and "lyman" in row["title_key"]
        )
        for row in group["records"]
    )


# ============================================================
# HTTP REQUESTS WITH RETRIES
# ============================================================

def format_error(exc):

    if isinstance(exc, HTTPError):
        return f"HTTP {exc.code}"

    return (
        f"{type(exc).__name__}: "
        f"{str(exc)[:100]}"
    )


def safe_public_https(url):

    parts = urlsplit(url)

    if (
        parts.scheme != "https"
        or not parts.hostname
        or parts.username
    ):
        return False

    hostname = parts.hostname.casefold()

    if (
        hostname in {
            "localhost",
            "localhost.localdomain"
        }
        or hostname.endswith(".local")
    ):
        return False

    try:

        if not ipaddress.ip_address(
            hostname
        ).is_global:
            return False

    except ValueError:
        pass

    return True


def wait_for_arxiv():

    global LAST_ARXIV_REQUEST

    if LAST_ARXIV_REQUEST:

        remaining = (
            3.2
            - (
                time.monotonic()
                - LAST_ARXIV_REQUEST
            )
        )

        if remaining > 0:
            time.sleep(remaining)

    LAST_ARXIV_REQUEST = time.monotonic()


def http_read(
    url,
    max_bytes=1_000_000,
    timeout=35,
    arxiv=False,
    headers=None
):

    if not safe_public_https(url):
        raise ValueError(
            "Invalid or unsafe HTTPS URL"
        )

    request_headers = {
        "User-Agent": USER_AGENT
    }

    request_headers.update(
        headers or {}
    )

    for attempt in range(3):

        if arxiv:
            wait_for_arxiv()

        try:

            with urlopen(
                Request(
                    url,
                    headers=request_headers
                ),
                timeout=timeout
            ) as response:

                if not safe_public_https(
                    response.geturl()
                ):
                    raise ValueError(
                        "Unsafe response URL"
                    )

                raw = response.read(
                    max_bytes + 1
                )

            if len(raw) > max_bytes:
                raise ValueError(
                    "Response exceeds "
                    f"{max_bytes // (1024 * 1024)} "
                    "MiB limit"
                )

            return raw

        except (
            HTTPError,
            URLError,
            TimeoutError,
            ConnectionError
        ) as exc:

            retryable = (
                not isinstance(exc, HTTPError)
                or exc.code in {
                    408,
                    429,
                    500,
                    502,
                    503,
                    504
                }
            )

            if (
                not retryable
                or attempt == 2
            ):
                raise

            time.sleep(
                2 * (attempt + 1)
            )

    raise RuntimeError(
        "Unreachable request retry logic"
    )


# ============================================================
# NASA ADS METADATA
# ============================================================

def fetch_ads(records, token):

    keys = sorted({
        ("bibcode", row["bibcode"])
        for row in records
        if row["bibcode"]
    })

    keys += sorted({
        ("doi", row["doi_key"])
        for row in records
        if row["doi_key"]
    })

    by_bibcode = {}
    by_doi = {}

    for offset in range(
        0,
        len(keys),
        15
    ):

        parts = []

        for field, value in keys[
            offset:offset + 15
        ]:

            escaped = (
                value.replace("\\", "\\\\")
                .replace('"', '\\"')
            )

            parts.append(
                f'{field}:"{escaped}"'
            )

        url = ADS_API + "?" + urlencode({
            "q": " OR ".join(parts),

            "fl": (
                "bibcode,doi,identifier,"
                "first_author,author_count,"
                "aff,citation_count"
            ),

            "rows": 200,
        })

        raw = http_read(
            url,
            max_bytes=8_000_000,
            timeout=75,
            headers={
                "Authorization": f"Bearer {token}",
                "Accept": "application/json"
            }
        )

        response = json.loads(
            raw
        ).get("response", {})

        docs = response.get("docs")

        if (
            not isinstance(docs, list)
            or response.get(
                "numFound", 0
            ) > len(docs)
        ):
            raise RuntimeError(
                "Truncated or malformed ADS response; "
                "no publication files updated"
            )

        for doc in docs:

            if doc.get("bibcode"):
                by_bibcode[
                    doc["bibcode"]
                ] = doc

            identifiers = (
                doc.get("doi") or []
            )

            if isinstance(
                identifiers,
                str
            ):
                identifiers = [
                    identifiers
                ]

            for identifier in identifiers:

                by_doi[
                    doi_key(identifier)
                ] = doc

    return by_bibcode, by_doi


def documents_for(group, ads):

    by_bibcode, by_doi = ads

    docs = []
    seen = set()

    for row in group["records"]:

        candidates = (
            by_bibcode.get(
                row["bibcode"]
            ),
            by_doi.get(
                row["doi_key"]
            )
        )

        for doc in candidates:

            if doc:

                key = (
                    doc.get("bibcode")
                    or id(doc)
                )

                if key not in seen:

                    seen.add(key)
                    docs.append(doc)

    return docs


def check_ads(docs):

    for doc in docs:

        affs = doc.get(
            "aff"
        ) or []

        if isinstance(affs, str):
            affs = [affs]

        for affiliation in affs:

            if qualifying_affiliation(
                affiliation
            ):
                return normalize_affiliation(
                    affiliation
                )[:300]

    return ""


# ============================================================
# ARXIV IDENTIFICATION
# ============================================================

def known_arxiv_id(group, docs):

    pieces = []

    for row in group["records"]:

        pieces.extend(
            clean(row.get(key))
            for key in (
                "DOI URL",
                "ADS URL",
                "Title",
                "Journal"
            )
        )

    for doc in docs:

        ids = (
            doc.get("identifier")
            or []
        )

        if isinstance(ids, str):
            ids = [ids]

        pieces += ids + [
            doc.get("bibcode", "")
        ]

    for piece in pieces:

        match = ARXIV_PATTERN.search(
            str(piece)
        )

        if match:
            return match.group(1)

        match = ARXIV_BIB_PATTERN.search(
            str(piece)
        )

        if match:
            return (
                f"{match.group(1)}."
                f"{match.group(2)}"
            )

    if is_priority(group):
        return PRIORITY_ARXIV

    return ""


def parse_arxiv(raw):

    root = ET.fromstring(raw)

    entries = []

    for entry in root.findall(
        ATOM + "entry"
    ):

        url = clean(
            entry.findtext(
                ATOM + "id"
            )
        )

        match = ARXIV_PATTERN.search(
            url
        )

        if not match:
            continue

        title = clean(
            entry.findtext(
                ATOM + "title"
            )
        )

        year_text = clean(
            entry.findtext(
                ATOM + "published"
            )
        )

        year = (
            int(year_text[:4])
            if re.match(
                r"^\d{4}",
                year_text
            )
            else 0
        )

        affs = []

        for author in entry.findall(
            ATOM + "author"
        ):

            affs += [
                normalize_affiliation(
                    item.text
                )
                for item in author.findall(
                    ARXIV_NS + "affiliation"
                )
                if item.text
            ]

        entries.append({
            "id": match.group(1),
            "title": title,
            "year": year,
            "affiliations": affs
        })

    return entries


def arxiv_by_id(identifier, title):

    url = ARXIV_API + "?" + urlencode({
        "id_list": identifier,
        "max_results": 1
    })

    entries = parse_arxiv(
        http_read(
            url,
            max_bytes=800_000,
            arxiv=True
        )
    )

    for entry in entries:

        if (
            entry["id"] == identifier
            and paper_title_matches(
                title,
                entry["title"]
            )
        ):
            return entry

    return None


def arxiv_by_title(title, year):

    # A verified title match is required.
    # Never trust the first search result blindly.

    words = re.findall(
        r"[a-zA-Z0-9]+",
        unicodedata.normalize(
            "NFKD",
            title
        )
    )

    if len(words) < 4:
        return None

    search_phrase = (
        " ".join(words[:8])
        .replace('"', "")
    )

    url = ARXIV_API + "?" + urlencode({
        "search_query": f'ti:"{search_phrase}"',
        "start": 0,
        "max_results": 10,
    })

    entries = parse_arxiv(
        http_read(
            url,
            max_bytes=1_500_000,
            arxiv=True
        )
    )

    entries = sorted(
        entries,
        key=lambda entry: SequenceMatcher(
            None,
            normalized_title(title),
            normalized_title(
                entry["title"]
            )
        ).ratio(),
        reverse=True
    )

    for entry in entries:

        title_matches = paper_title_matches(
            title,
            entry["title"]
        )

        year_matches = (
            not entry["year"]
            or abs(
                entry["year"] - year
            ) <= 4
        )

        if (
            title_matches
            and year_matches
        ):
            return entry

    return None


# ============================================================
# OPENALEX AFFILIATION METADATA
# ============================================================

def lookup_openalex(group):

    # DOI is an exact identifier.
    # Do not guess OpenAlex records by title alone.

    dois = [
        row["doi_key"]
        for row in group["records"]
        if (
            row["doi_key"]
            and not row["doi_key"].startswith(
                "10.48550/arxiv."
            )
        )
    ]

    if not dois:
        return None

    doi = dois[0]

    url = (
        "https://api.openalex.org/works/"
        "https://doi.org/"
        + quote(
            doi,
            safe="/"
        )
    )

    try:

        raw = http_read(
            url,
            max_bytes=3_000_000,
            timeout=30,
            headers={
                "Accept": "application/json"
            }
        )

    except HTTPError as exc:

        if exc.code == 404:
            return None

        raise

    obj = json.loads(raw)

    expected = preferred_record(
        group["records"]
    )["Title"]

    if (
        obj.get("title")
        and not paper_title_matches(
            expected,
            obj["title"]
        )
    ):
        return None

    return obj


def openalex_affiliation(obj):

    if not obj:
        return ""

    for author in (
        obj.get("authorships")
        or []
    ):

        for affiliation in (
            author.get(
                "raw_affiliation_strings"
            )
            or []
        ):

            if qualifying_affiliation(
                affiliation
            ):
                return normalize_affiliation(
                    affiliation
                )[:300]

        for inst in (
            author.get("institutions")
            or []
        ):

            institution = (
                inst.get("display_name")
                or ""
            )

            if qualifying_affiliation(
                institution
            ):
                return institution[:300]

    return ""


def openalex_pdf_urls(obj):

    if not obj:
        return []

    locations = [
        obj.get(
            "best_oa_location"
        ) or {}
    ] + (
        obj.get("locations")
        or []
    )

    urls = []

    for location in locations:

        url = (
            location.get("pdf_url")
            or ""
        )

        if (
            safe_public_https(url)
            and url not in urls
        ):
            urls.append(url)

    return urls[:3]


# ============================================================
# FULL PDF AFFILIATION EXTRACTION
#
# IMPORTANT:
# Examine ALL pages of the PDF.
#
# Supports:
#   1. First-page author affiliations.
#   2. Explicit affiliation sections.
#   3. Numbered institution lists anywhere in the PDF.
#
# This is particularly useful for LIGO collaboration
# papers with affiliations near the end of the PDF.
# ============================================================

def pdf_header_affiliation(url):

    """Check all PDF pages for author-affiliation evidence.

    A qualifying institution must appear in a recognizable
    author-affiliation context.

    Ordinary mentions in references, acknowledgments,
    or the main text are not sufficient.
    """

    raw = http_read(
        url,
        max_bytes=MAX_PDF_BYTES,
        timeout=65,
        arxiv=(
            "arxiv.org"
            in (
                urlsplit(url).hostname
                or ""
            )
        ),
        headers={
            "Accept": "application/pdf"
        },
    )

    if not raw.lstrip().startswith(
        b"%PDF"
    ):
        raise ValueError(
            "URL did not provide a readable PDF"
        )

    # Examples of numbered author affiliations:
    #
    # 109 Kenyon College, Gambier, Ohio
    # 110 Missouri University of Science and Technology
    # 111 Indian Institute of Technology Madras
    #
    # Sometimes the superscript number is attached
    # directly to the institutional name.

    number_and_name = re.compile(
        r"^\s*(\d{1,4})(?!\d)"
        r"(?:\s+|(?=[A-Za-z]))"
        r"([A-Za-z].*)$"
    )

    number_only = re.compile(
        r"^\s*\d{1,4}\s*$"
    )

    institution_word = re.compile(
        r"\b(?:university|universit\w*|college|"
        r"institute|institut\w*|laborator\w*|"
        r"observator\w*|department|school|academy|"
        r"research\s+cent(?:er|re)|INFN|CNRS)\b",
        re.IGNORECASE
    )

    def numbered_affiliation_match(page_text):

        """Find qualifying institutions in numbered lists."""

        lines = [
            line.strip()
            for line in page_text.splitlines()
            if line.strip()
        ]

        entries = []

        for index, line in enumerate(lines):

            match = number_and_name.match(line)

            if match:

                beginning = match.group(2)

            elif (
                number_only.match(line)
                and index + 1 < len(lines)
            ):

                beginning = lines[index + 1]

            else:
                continue

            continuation = []

            first_next = index + (
                2
                if number_only.match(line)
                else 1
            )

            # Allow an institutional address to
            # continue over several PDF lines.
            #
            # Stop when the next numbered entry begins.

            for next_line in lines[
                first_next:first_next + 3
            ]:

                if (
                    number_and_name.match(next_line)
                    or number_only.match(next_line)
                ):
                    break

                continuation.append(next_line)

            entry = normalize_affiliation(
                " ".join(
                    [beginning] + continuation
                )
            )

            if institution_word.search(entry):
                entries.append(entry)

        # Require multiple numbered institutions.
        # This helps avoid mistaking one numbered
        # reference for an affiliation.

        if len(entries) < 3:
            return ""

        for entry in entries:

            if qualifying_affiliation(entry):
                return entry[:320]

        return ""

    with pymupdf.open(
        stream=raw,
        filetype="pdf"
    ) as document:

        in_affiliation_section = False

        front_matter = True

        # ----------------------------------------------------
        # CRITICAL IMPROVEMENT:
        #
        # Examine every page, including page 41 and
        # the final pages of collaboration papers.
        # ----------------------------------------------------

        for page_number in range(
            len(document)
        ):

            text = document[
                page_number
            ].get_text(
                "text",
                sort=True
            )

            if not text.strip():
                continue

            # ------------------------------------------------
            # Method 1:
            # Numbered collaboration affiliations
            # anywhere in the PDF.
            # ------------------------------------------------

            match = numbered_affiliation_match(
                text
            )

            if match:

                return (
                    match,
                    f"{url}#page={page_number + 1}"
                )

            candidates = []

            # ------------------------------------------------
            # Method 2:
            # Standard first-page affiliations.
            # ------------------------------------------------

            if (
                front_matter
                and page_number < 3
            ):

                abstract = (
                    ABSTRACT_HEADING.search(
                        text
                    )
                )

                candidates.append(
                    text[:abstract.start()]
                    if abstract
                    else text[:9000]
                )

                if abstract:
                    front_matter = False

            else:
                front_matter = False

            # ------------------------------------------------
            # Method 3:
            # Explicit affiliation sections anywhere
            # in the PDF.
            # ------------------------------------------------

            heading = (
                AFFILIATION_HEADING.search(
                    text
                )
            )

            if heading:

                in_affiliation_section = True

                candidates.append(
                    text[
                        heading.end():
                    ]
                )

            elif in_affiliation_section:

                if SECTION_HEADING.search(
                    text[:700]
                ):

                    in_affiliation_section = False

                else:

                    candidates.append(text)

            # ------------------------------------------------
            # Check candidate author-affiliation text.
            # ------------------------------------------------

            for candidate in candidates:

                normalized = normalize_affiliation(
                    candidate
                )

                for pattern in AFFILIATION_PATTERNS:

                    match = pattern.search(
                        normalized
                    )

                    if match:

                        excerpt = normalized[
                            max(
                                0,
                                match.start() - 70
                            ):
                            match.end() + 130
                        ]

                        return (
                            excerpt[:320],
                            f"{url}#page={page_number + 1}"
                        )

    return "", ""


# ============================================================
# AFFILIATION CACHE
# ============================================================

def cluster_cache_key(group):

    row = preferred_record(
        group["records"]
    )

    if row["doi_key"]:
        return (
            "doi:"
            + row["doi_key"]
        )

    if row["bibcode"]:
        return (
            "ads:"
            + row["bibcode"]
        )

    return (
        "title:"
        + row["title_key"]
    )


def load_cache():

    if CACHE_FILE.is_file():

        value = json.loads(
            CACHE_FILE.read_text(
                encoding="utf-8"
            )
        )

        if isinstance(
            value,
            dict
        ):
            return value

    return {}


def save_cache(cache):

    CACHE_FILE.parent.mkdir(
        parents=True,
        exist_ok=True
    )

    temporary = (
        CACHE_FILE.with_suffix(
            ".json.tmp"
        )
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
# OPTIONAL MANUAL AFFILIATION DECISIONS
# ============================================================

def load_decisions():

    if not DECISIONS_FILE.is_file():
        return {}

    raw = json.loads(
        DECISIONS_FILE.read_text(
            encoding="utf-8"
        )
    )

    results = {}

    for item in raw.get(
        "decisions",
        []
    ):

        verdict = item.get(
            "decision"
        )

        identifier = (
            doi_key(item.get("doi"))
            if item.get("doi")
            else ""
        )

        key = (
            "doi:" + identifier
            if identifier
            else "arxiv:"
            + clean(item.get("arxiv"))
        )

        evidence_url = clean(
            item.get("evidence_url")
        )

        if (
            verdict not in {
                "include",
                "exclude"
            }
            or not evidence_url.startswith(
                "https://"
            )
        ):

            raise ValueError(
                "Manual affiliation decisions require "
                "include/exclude and HTTPS evidence_url"
            )

        results[key] = item

    return results


def check_decision(group, decisions):

    keys = [
        "doi:" + row["doi_key"]
        for row in group["records"]
        if row["doi_key"]
    ]

    for row in group["records"]:

        match = ARXIV_PATTERN.search(
            " ".join(
                clean(row.get(k))
                for k in (
                    "DOI URL",
                    "ADS URL"
                )
            )
        )

        if match:
            keys.append(
                "arxiv:"
                + match.group(1)
            )

    for key in keys:

        if key in decisions:

            item = decisions[key]

            return (
                "verified"
                if item["decision"] == "include"
                else "excluded",

                "manual review",

                clean(
                    item.get("reason")
                    or "Reviewed affiliation decision"
                ),

                clean(
                    item["evidence_url"]
                )
            )

    return None


def cached_result(old):

    if not isinstance(
        old,
        dict
    ):
        return False

    # Preserve previously verified matches.

    if old.get("status") == "verified":
        return True

    # Retry old inconclusive results using
    # the new full-PDF checker.

    if (
        old.get("cache_version")
        != CACHE_VERSION
    ):
        return False

    try:

        stamp = datetime.fromisoformat(
            old["checked_at"]
        )

        age = (
            datetime.now(timezone.utc)
            - stamp
        ).total_seconds() / 86400

    except (
        KeyError,
        ValueError,
        TypeError
    ):
        return False

    days = (
        1
        if old.get("status") == "error"
        else 30
    )

    return age < days


# ============================================================
# COMBINED AFFILIATION VERIFICATION
# ============================================================

def verify(
    group,
    ads,
    cache,
    decisions,
    budget
):

    docs = documents_for(
        group,
        ads
    )

    identifier = known_arxiv_id(
        group,
        docs
    )

    # --------------------------------------------------------
    # 1. Honor evidence-based manual decisions.
    # --------------------------------------------------------

    override = check_decision(
        group,
        decisions
    )

    if override:

        return (
            *override,
            identifier
        )

    # --------------------------------------------------------
    # 2. Check NASA ADS.
    # --------------------------------------------------------

    hit = check_ads(docs)

    if hit:

        return (
            "verified",
            "NASA ADS",
            hit,
            "",
            identifier
        )

    key = cluster_cache_key(
        group
    )

    old = cache.get(
        key,
        {}
    )

    # --------------------------------------------------------
    # 3. Reuse cached results when appropriate.
    # --------------------------------------------------------

    if cached_result(old):

        return (
            old["status"],

            old.get(
                "source",
                "cached"
            ),

            old.get(
                "evidence",
                ""
            ),

            old.get(
                "evidence_url",
                ""
            ),

            old.get(
                "arxiv_id"
            ) or identifier
        )

    # --------------------------------------------------------
    # 4. Limit expensive external checks per run.
    # --------------------------------------------------------

    if budget["used"] >= MAX_CHECKS:

        return (
            "pending",
            "budget",
            "Waiting for next daily run",
            "",
            identifier
        )

    budget["used"] += 1

    chosen = preferred_record(
        group["records"]
    )

    title = chosen["Title"]

    year = int(
        chosen["Year"]
    )

    errors = []

    sources_checked = []

    openalex = None

    arxiv_entry = None

    evidence_urls = []

    # --------------------------------------------------------
    # 5. Check OpenAlex.
    # --------------------------------------------------------

    try:

        openalex = lookup_openalex(
            group
        )

        if openalex:

            sources_checked.append(
                "OpenAlex"
            )

            hit = openalex_affiliation(
                openalex
            )

            if hit:

                result = (
                    "verified",
                    "OpenAlex",
                    hit,
                    clean(
                        openalex.get("id")
                    ),
                    identifier
                )

                return remember_result(
                    cache,
                    key,
                    result
                )

    except (
        HTTPError,
        URLError,
        TimeoutError,
        ValueError,
        json.JSONDecodeError
    ) as exc:

        errors.append(
            "OpenAlex: "
            + format_error(exc)
        )

    # --------------------------------------------------------
    # 6. Identify arXiv paper.
    #
    # First try the known identifier.
    # Otherwise search by publication title.
    # --------------------------------------------------------

    try:

        if identifier:

            arxiv_entry = arxiv_by_id(
                identifier,
                title
            )

            if not arxiv_entry:

                errors.append(
                    "arXiv: known ID did not match title"
                )

                identifier = ""

        if not arxiv_entry:

            arxiv_entry = arxiv_by_title(
                title,
                year
            )

            if arxiv_entry:

                identifier = (
                    arxiv_entry["id"]
                )

        if arxiv_entry:

            sources_checked.append(
                "arXiv metadata"
            )

            for affiliation in (
                arxiv_entry["affiliations"]
            ):

                if qualifying_affiliation(
                    affiliation
                ):

                    result = (
                        "verified",
                        "arXiv author metadata",
                        affiliation[:320],
                        (
                            "https://arxiv.org/abs/"
                            + identifier
                        ),
                        identifier
                    )

                    return remember_result(
                        cache,
                        key,
                        result
                    )

    except (
        HTTPError,
        URLError,
        TimeoutError,
        ET.ParseError,
        ValueError
    ) as exc:

        errors.append(
            "arXiv: "
            + format_error(exc)
        )

    # --------------------------------------------------------
    # 7. Check accessible PDFs.
    #
    # Prefer arXiv, then available publisher PDFs.
    # --------------------------------------------------------

    pdf_urls = (
        [
            f"https://arxiv.org/pdf/{identifier}"
        ]
        if identifier
        else []
    )

    pdf_urls += openalex_pdf_urls(
        openalex
    )

    seen = set()

    for url in pdf_urls:

        if url in seen:
            continue

        seen.add(url)

        try:

            hit, evidence_url = (
                pdf_header_affiliation(
                    url
                )
            )

            sources_checked.append(
                "PDF inspected"
            )

            if hit:

                result = (
                    "verified",
                    "PDF affiliation",
                    hit,
                    evidence_url,
                    identifier
                )

                return remember_result(
                    cache,
                    key,
                    result
                )

            evidence_urls.append(
                url
            )

        except (
            HTTPError,
            URLError,
            TimeoutError,
            ValueError,
            RuntimeError,
            pymupdf.FileDataError
        ) as exc:

            errors.append(
                "PDF: "
                + format_error(exc)
            )

    # --------------------------------------------------------
    # 8. Inconclusive verification.
    #
    # Absence of a detected affiliation does not
    # prove that the paper is non-IMAC.
    # --------------------------------------------------------

    if sources_checked:

        result = (
            "needs_review",

            ", ".join(
                sources_checked
            ),

            (
                "No matching author affiliation "
                "established; "
                + "; ".join(errors)
            )[:320],

            (
                evidence_urls[0]
                if evidence_urls
                else ""
            ),

            identifier
        )

    else:

        result = (
            (
                "error"
                if errors
                else "needs_review"
            ),

            "retrieval",

            (
                "; ".join(errors)
                or "No usable source found"
            )[:320],

            "",

            identifier
        )

    return remember_result(
        cache,
        key,
        result
    )


def remember_result(
    cache,
    key,
    result
):

    (
        status,
        source,
        evidence,
        evidence_url,
        identifier
    ) = result

    cache[key] = {
        "cache_version": CACHE_VERSION,

        "status": status,

        "source": source,

        "evidence": evidence[:320],

        "evidence_url": evidence_url,

        "arxiv_id": identifier,

        "checked_at": datetime.now(
            timezone.utc
        ).isoformat(),
    }

    return result


# ============================================================
# FORMAT AUTHOR NAMES
# ============================================================

def authors_label(
    group,
    docs,
    order
):

    names = sorted(
        group["researchers"],
        key=lambda name: order.get(
            name,
            9999
        )
    )

    selected = ", ".join(
        (
            name.split()[0][0]
            + ". "
            + name.split()[-1]
        )
        if len(name.split()) > 1
        else name
        for name in names
    )

    for doc in docs:

        first = (
            doc.get("first_author")
            or ""
        )

        if isinstance(first, list):

            first = (
                first[0]
                if first
                else ""
            )

        if first:

            surname = clean(
                first
            ).split(",")[0]

            try:

                many = (
                    int(
                        doc.get(
                            "author_count"
                        ) or 2
                    ) > 1
                )

            except (
                TypeError,
                ValueError
            ):

                many = True

            return (
                f"{surname}"
                f"{' et al.' if many else ''}"
                f" (incl. {selected})"
            )

    return (
        f"IMAC contributors: {selected}"
    )


# ============================================================
# GENERATE PUBLICATION TABLE ROWS
# ============================================================

def publication_row(
    group,
    ads,
    order
):

    chosen = preferred_record(
        group["records"]
    )

    docs = documents_for(
        group,
        ads
    )

    # Avoid adding the same paper's journal
    # and arXiv citation counts together.

    counts = [
        int(row["Citation (ADS)"])
        for row in group["records"]
        if row["Citation (ADS)"].isdigit()
    ]

    counts += [
        int(doc["citation_count"])
        for doc in docs
        if str(
            doc.get(
                "citation_count",
                ""
            )
        ).isdigit()
    ]

    return {
        "Title": html.escape(
            chosen["Title"],
            quote=False
        ),

        "Authors": html.escape(
            authors_label(
                group,
                docs,
                order
            ),
            quote=False
        ),

        "Journal": html.escape(
            chosen["Journal"],
            quote=False
        ),

        "Citation (ADS)": (
            max(counts)
            if counts
            else ""
        ),

        "DOI URL": chosen.get(
            "DOI URL",
            ""
        ),

        "ADS URL": chosen.get(
            "ADS URL",
            ""
        )
    }


# ============================================================
# WRITE CSV FILES
# ============================================================

def write_csv(
    path,
    rows,
    cols
):

    tmp = path.with_suffix(
        ".csv.tmp"
    )

    with tmp.open(
        "w",
        newline="",
        encoding="utf-8"
    ) as handle:

        writer = csv.DictWriter(
            handle,
            fieldnames=cols
        )

        writer.writeheader()

        writer.writerows(rows)

    os.replace(
        tmp,
        path
    )


# ============================================================
# GENERATE OVERALL IMAC STATISTICS
# ============================================================

def write_summary(
    output,
    annual,
    statuses
):

    current = datetime.now(
        timezone.utc
    ).year

    papers = [
        row
        for year, rows in annual.items()
        if START_YEAR <= int(year) <= current
        for row in rows
    ]

    citation_counts = [
        int(str(row["Citation (ADS)"]))
        for row in papers
        if str(
            row["Citation (ADS)"]
        ).isdigit()
    ]

    n = len(papers)

    total = sum(
        citation_counts
    )

    unresolved = sum(
        statuses[s]
        for s in (
            "pending",
            "needs_review",
            "error"
        )
    )

    noun = (
        "article"
        if n == 1
        else "articles"
    )

    # Use preliminary wording until all
    # affiliation cases have been resolved.

    if unresolved:

        sentence = (
            f"So far, {n:,} IMAC-affiliated "
            f"{noun} have been verified, "
            f"receiving {total:,} citations "
            "according to NASA ADS "
            "(preliminary)."
        )

    else:

        sentence = (
            f"IMAC published a total of "
            f"{n:,} {noun}, cited a total of "
            f"{total:,} times "
            "(according to NASA ADS)."
        )

    detail = (
        f"2019–{current}; verified institutional "
        f"affiliations. ADS citation counts "
        f"available for "
        f"{len(citation_counts)}/{n} articles. "
    )

    if unresolved:

        detail += (
            f"PRELIMINARY: {unresolved} "
            "publications remain unresolved. "
        )

    detail += (
        "Citation counts are cumulative to date."
    )

    # --------------------------------------------------------
    # CSV SUMMARY
    # --------------------------------------------------------

    with (
        output / "summary_statistics.csv"
    ).open(
        "w",
        newline="",
        encoding="utf-8"
    ) as handle:

        writer = csv.writer(handle)

        writer.writerow([
            "IMAC Publication Summary"
        ])

        writer.writerow([
            sentence
        ])

    # --------------------------------------------------------
    # JSON SUMMARY
    # --------------------------------------------------------

    (
        output / "summary.json"
    ).write_text(
        json.dumps(
            {
                "start_year": START_YEAR,

                "end_year": current,

                "published_articles": n,

                "ads_citations": total,

                "papers_with_ads_data": (
                    len(citation_counts)
                ),

                "unresolved_affiliations": unresolved,

                "preliminary": bool(unresolved),

                "verification_statuses": dict(
                    statuses
                ),

                "summary": sentence,

                "note": detail
            },
            indent=2
        ),
        encoding="utf-8"
    )

    # --------------------------------------------------------
    # HTML SUMMARY FOR TERMINALFOUR
    # --------------------------------------------------------

    (
        output / "summary.html"
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
        f"<p>{html.escape(sentence)}</p>"
        f"<small>{html.escape(detail)}</small>"
        "</body>"
        "</html>",
        encoding="utf-8"
    )

    print(sentence)
    print(detail)

    return n, unresolved


# ============================================================
# MAIN PROGRAM
# ============================================================

def main():

    token = os.getenv(
        "ADS_API_TOKEN"
    )

    if not token:
        raise RuntimeError(
            "ADS_API_TOKEN secret is missing"
        )

    if MODE not in {
        "preview",
        "live"
    }:
        raise ValueError(
            "IMAC_OUTPUT_MODE must be preview or live"
        )

    if MAX_CHECKS < 0:
        raise ValueError(
            "IMAC_MAX_NEW_CHECKS cannot be negative"
        )

    # --------------------------------------------------------
    # Step 1: Read researcher publication data
    # --------------------------------------------------------

    researchers, records = load_records()

    # --------------------------------------------------------
    # Step 2: Remove duplicate publications
    # --------------------------------------------------------

    groups = collapse(
        records
    )

    year_now = datetime.now(
        timezone.utc
    ).year

    # --------------------------------------------------------
    # Step 3: Include publications from 2019 onward
    # --------------------------------------------------------

    groups = [
        group
        for group in groups
        if START_YEAR <= int(
            preferred_record(
                group["records"]
            )["Year"]
        ) <= year_now
    ]

    print(
        f"Unique 2019–{year_now} works: "
        f"{len(groups)}"
    )

    selected_records = [
        row
        for group in groups
        for row in group["records"]
    ]

    # --------------------------------------------------------
    # Step 4: Retrieve NASA ADS metadata
    # --------------------------------------------------------

    ads = fetch_ads(
        selected_records,
        token
    )

    cache = load_cache()

    decisions = load_decisions()

    order = {
        person["name"]: i
        for i, person in enumerate(
            researchers
        )
    }

    statuses = Counter()

    budget = {
        "used": 0
    }

    annual = defaultdict(list)

    preprints = []

    audit = []

    # --------------------------------------------------------
    # Step 5: Determine verification order
    #
    # The priority test paper is checked first.
    # Output ordering is handled separately.
    # --------------------------------------------------------

    groups.sort(
        key=lambda group: (
            is_priority(group),

            int(
                preferred_record(
                    group["records"]
                )["Year"]
            )
        ),
        reverse=True
    )

    # --------------------------------------------------------
    # Step 6: Verify institutional affiliations
    # --------------------------------------------------------

    for group in groups:

        chosen = preferred_record(
            group["records"]
        )

        (
            status,
            source,
            evidence,
            evidence_url,
            identifier
        ) = verify(
            group,
            ads,
            cache,
            decisions,
            budget
        )

        statuses[status] += 1

        audit.append({
            "Year": chosen["Year"],

            "Title": chosen["Title"],

            "Status": status,

            "Source": source,

            "Evidence": evidence,

            "Evidence URL": evidence_url,

            "arXiv": identifier,

            "DOI URL": chosen.get(
                "DOI URL",
                ""
            ),

            "ADS URL": chosen.get(
                "ADS URL",
                ""
            ),
        })

        if is_priority(group):

            print(
                f"PRIORITY PAPER arXiv:"
                f"{PRIORITY_ARXIV}: "
                f"{status} | {source} | "
                f"{evidence[:160]}"
            )

        if status != "verified":
            continue

        row = publication_row(
            group,
            ads,
            order
        )

        if chosen["preprint"]:

            if int(
                chosen["Year"]
            ) >= year_now - 1:

                preprints.append(row)

        elif chosen["Journal"]:

            annual[
                chosen["Year"]
            ].append(row)

    # --------------------------------------------------------
    # Step 7: Select preview or live output
    # --------------------------------------------------------

    output = (
        PREVIEW_DIR
        if MODE == "preview"
        else LIVE_DIR
    )

    verified_count = sum(
        len(items)
        for items in annual.values()
    )

    unresolved = sum(
        statuses[s]
        for s in (
            "pending",
            "needs_review",
            "error"
        )
    )

    # Never publish incomplete live data.

    if (
        MODE == "live"
        and (
            verified_count == 0
            or unresolved
        )
    ):

        raise RuntimeError(
            "Live update blocked: unresolved "
            "affiliation checks remain"
        )

    output.mkdir(
        parents=True,
        exist_ok=True
    )

    # Save verification results for future daily runs.

    save_cache(cache)

    # --------------------------------------------------------
    # Step 8: Generate yearly publication tables
    #
    # 2019 onward only.
    # No yearly summary rows.
    # --------------------------------------------------------

    years = {
        str(y)
        for y in range(
            START_YEAR,
            year_now + 1
        )
    } | set(annual)

    for path in LIVE_DIR.glob(
        "publications_*.csv"
    ):

        match = re.fullmatch(
            r"publications_(\d{4})\.csv",
            path.name
        )

        if (
            match
            and START_YEAR
            <= int(match.group(1))
            <= year_now
        ):

            years.add(
                match.group(1)
            )

    for year in sorted(
        years,
        reverse=True
    ):

        rows = sorted(
            annual.get(year, []),
            key=lambda row: row[
                "Title"
            ].casefold()
        )

        write_csv(
            output / f"publications_{year}.csv",
            rows,
            CSV_COLUMNS
        )

        print(
            f"{year}: {len(rows)} "
            "verified published papers"
        )

    # --------------------------------------------------------
    # Step 9: Generate recent preprints
    # --------------------------------------------------------

    write_csv(
        output / "recent_preprints.csv",

        sorted(
            preprints,
            key=lambda row: row[
                "Title"
            ].casefold()
        ),

        CSV_COLUMNS
    )

    # --------------------------------------------------------
    # Step 10: Generate overall statistics
    # --------------------------------------------------------

    write_summary(
        output,
        annual,
        statuses
    )

    # --------------------------------------------------------
    # Step 11: Sort the affiliation audit
    #
    # Newest year first.
    # Alphabetical by title within each year.
    # --------------------------------------------------------

    audit.sort(
        key=lambda row: (
            -int(row["Year"]),
            row["Title"].casefold()
        )
    )

    # --------------------------------------------------------
    # Step 12: Save complete affiliation audit
    # --------------------------------------------------------

    write_csv(
        output / "affiliation_audit.csv",
        audit,
        AUDIT_COLUMNS
    )

    # --------------------------------------------------------
    # Step 13: Save unresolved cases
    # --------------------------------------------------------

    write_csv(
        output / "affiliation_review.csv",

        [
            row
            for row in audit
            if row["Status"] not in {
                "verified",
                "excluded"
            }
        ],

        AUDIT_COLUMNS
    )

    # --------------------------------------------------------
    # Step 14: Print results
    # --------------------------------------------------------

    print(
        "Affiliation statuses:",
        dict(statuses)
    )

    print(
        f"New fallback checks: "
        f"{budget['used']}/{MAX_CHECKS}; "
        f"mode: {MODE}; "
        f"directory: {output}"
    )


if __name__ == "__main__":
    main()
