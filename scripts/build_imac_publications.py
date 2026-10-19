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

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "docs" / "publications"
LIVE_DIR = ROOT / "docs" / "imac"
PREVIEW_DIR = ROOT / "docs" / "imac_affiliation_preview"
CACHE_FILE = PREVIEW_DIR / "affiliation_cache.json"
DECISIONS_FILE = ROOT / "affiliation_decisions.json"  # optional, evidence-based
RESEARCHERS_FILE = ROOT / "researchers.json"
ADS_API = "https://api.adsabs.harvard.edu/v1/search/query"
ARXIV_API = "https://export.arxiv.org/api/query"
START_YEAR = 2019  # inclusive
MODE = os.getenv("IMAC_OUTPUT_MODE", "preview").strip().lower()
MAX_CHECKS = int(os.getenv("IMAC_MAX_NEW_CHECKS", "30"))
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
