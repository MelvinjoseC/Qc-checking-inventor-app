import re
import sys
import json
import logging
from pathlib import Path
from enum import Enum
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Tuple, Optional, Set, Any, Union

logger = logging.getLogger("qc_logic")


class PDFQCError(Exception):
    """Base exception for all PDF QC errors."""
    pass


class InvalidConfigError(PDFQCError):
    """Exception raised when configuration is invalid or missing required values."""
    pass


class OCRNotFoundError(PDFQCError):
    """Exception raised when OCR dependencies are missing."""
    pass


class QCStatus(str, Enum):
    """Enumeration of quality control check status."""
    PASS = "PASS"
    FAIL = "FAIL"
    WARNING = "WARNING"
    SKIPPED = "SKIPPED"


class ToleranceMode(str, Enum):
    """Evaluation mode for measurement tolerances."""
    ABSOLUTE = "absolute"
    PERCENTAGE = "percentage"



@dataclass
class TableAnchor:
    """Bounding box coordinates for a table cell anchor."""
    x0: float = 0.0
    x1: float = 0.0
    top: float = 0.0
    bottom: float = 0.0

    def to_dict(self) -> Dict[str, float]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Optional[Dict[str, Any]]) -> Optional["TableAnchor"]:
        if not data:
            return None
        return cls(
            x0=float(data.get("x0", 0.0)),
            x1=float(data.get("x1", 0.0)),
            top=float(data.get("top", 0.0)),
            bottom=float(data.get("bottom", 0.0))
        )


@dataclass
class BOMItem:
    """Represents a single Bill of Materials line item parsed from drawing."""
    pos: str
    description: str
    length: Optional[float] = None
    length_display: Optional[str] = None
    length_options: List[float] = field(default_factory=list)
    table_id: Optional[int] = None
    table_label: Optional[str] = None
    quantity: Optional[float] = None
    quantity_display: Optional[str] = None
    callout_quantity_text: Optional[str] = None
    thickness: Optional[float] = None
    thickness_display: Optional[str] = None
    table_page: Optional[int] = None
    table_anchor: Optional[Union[TableAnchor, Dict[str, float]]] = None

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        if isinstance(self.table_anchor, TableAnchor):
            d["table_anchor"] = self.table_anchor.to_dict()
        return d

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "BOMItem":
        anchor = data.get("table_anchor")
        if isinstance(anchor, dict):
            anchor = TableAnchor.from_dict(anchor)
        return cls(
            pos=str(data.get("pos", "")),
            description=str(data.get("description", "")),
            length=data.get("length"),
            length_display=data.get("length_display"),
            length_options=data.get("length_options") or [],
            table_id=data.get("table_id"),
            table_label=data.get("table_label"),
            quantity=data.get("quantity"),
            quantity_display=data.get("quantity_display"),
            callout_quantity_text=data.get("callout_quantity_text"),
            thickness=data.get("thickness"),
            thickness_display=data.get("thickness_display"),
            table_page=data.get("table_page"),
            table_anchor=anchor
        )


@dataclass
class QCValidationResult:
    """Result of validating a BOM line item against drawing annotations."""
    pos: str
    description: str
    status: str = QCStatus.FAIL.value
    quantity: Optional[float] = None
    quantity_display: Optional[str] = None
    length: Optional[float] = None
    length_display: Optional[str] = None
    length_found: bool = False
    drawing_length: Optional[float] = None
    length_match: bool = False
    thickness: Optional[float] = None
    thickness_display: Optional[str] = None
    thickness_found: bool = False
    drawing_thickness: Optional[float] = None
    thickness_match: bool = False
    details: str = ""
    page: Optional[int] = None

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "QCValidationResult":
        return cls(
            pos=str(data.get("pos", "")),
            description=str(data.get("description", "")),
            status=str(data.get("status", QCStatus.FAIL.value)),
            quantity=data.get("quantity"),
            quantity_display=data.get("quantity_display"),
            length=data.get("length"),
            length_display=data.get("length_display"),
            length_found=bool(data.get("length_found", False)),
            drawing_length=data.get("drawing_length"),
            length_match=bool(data.get("length_match", False)),
            thickness=data.get("thickness"),
            thickness_display=data.get("thickness_display"),
            thickness_found=bool(data.get("thickness_found", False)),
            drawing_thickness=data.get("drawing_thickness"),
            thickness_match=bool(data.get("thickness_match", False)),
            details=str(data.get("details", "")),
            page=data.get("page")
        )


@dataclass
class CheckSummary:
    """Aggregated summary of quality control check results."""
    total_items: int = 0
    passed: int = 0
    failed: int = 0
    warnings: int = 0
    pass_rate: float = 0.0

    @classmethod
    def from_results(cls, results: List[Union[QCValidationResult, Dict[str, Any]]]) -> "CheckSummary":
        total = len(results)
        passed = 0
        failed = 0
        warnings = 0
        for r in results:
            status = r.status if isinstance(r, QCValidationResult) else r.get("status", "")
            if status == QCStatus.PASS.value:
                passed += 1
            elif status == QCStatus.WARNING.value:
                warnings += 1
            else:
                failed += 1
        rate = (passed / total * 100.0) if total > 0 else 0.0
        return cls(
            total_items=total,
            passed=passed,
            failed=failed,
            warnings=warnings,
            pass_rate=round(rate, 2)
        )



DEFAULT_CONFIG = {
    "tolerance": 0.5,
    "default_dpi": 300,
    "poppler_path": "",
    "tesseract_path": ""
}

def validate_config(config: Any) -> Dict[str, Any]:
    """
    Validate config dict structure and values, falling back to defaults if invalid.
    """
    if not isinstance(config, dict):
        return DEFAULT_CONFIG.copy()
    
    validated = DEFAULT_CONFIG.copy()
    if "tolerance" in config:
        try:
            tolerance = float(config["tolerance"])
            if tolerance >= 0:
                validated["tolerance"] = tolerance
        except (ValueError, TypeError):
            pass
            
    if "default_dpi" in config:
        try:
            dpi = int(config["default_dpi"])
            if dpi > 0:
                validated["default_dpi"] = dpi
        except (ValueError, TypeError):
            pass
            
    if "poppler_path" in config:
        validated["poppler_path"] = str(config["poppler_path"])
        
    if "tesseract_path" in config:
        validated["tesseract_path"] = str(config["tesseract_path"])
        
    return validated


def load_config(path: Union[str, Path] = 'config.json') -> Dict[str, Any]:
    try:
        p = Path(path)
        if p.exists():
            with open(p, 'r', encoding='utf-8') as f:
                config = json.load(f)
                return validate_config(config)
    except Exception as e:
        logger.warning("Failed to load config, using defaults: %s", e)
    return DEFAULT_CONFIG.copy()

def save_config(config: Dict[str, Any], path: Union[str, Path] = 'config.json') -> bool:
    try:
        p = Path(path)
        with open(p, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=4)
        return True
    except Exception as e:
        logger.error("Failed to save config to %s: %s", path, e)
        return False


def load_spellcheck_allowlist(path: Union[str, Path] = 'spellcheck_allowlist.txt') -> Set[str]:
    words = set()
    try:
        p = Path(path)
        if p.exists():
            with open(p, 'r', encoding='utf-8') as f:
                for line in f:
                    w = line.strip().lower()
                    if w and not w.startswith('#'):
                        words.add(w)
    except Exception as e:
        logger.warning("Failed to load spellcheck allowlist from %s: %s", path, e)
    return words


# --- Optional dependencies for text extraction and OCR ---
try:
    import PyPDF2
except Exception:
    PyPDF2 = None

try:
    from pdf2image import convert_from_path
    import pytesseract
except Exception:
    convert_from_path = None
    pytesseract = None

try:
    import pdfplumber
except Exception:
    pdfplumber = None


def extract_text_from_pdf(path: Union[str, Path]) -> str:
    """Try to extract text with PyPDF2. Returns combined text of all pages (may be empty)."""
    p = Path(path)
    if not p.exists():
        raise PDFQCError(f"PDF file does not exist: {path}")
    text = ""
    if PyPDF2 is None:
        logger.warning("PyPDF2 is not installed, direct extraction unavailable")
        return text
    try:
        with open(path, "rb") as f:
            reader = PyPDF2.PdfReader(f)
            for p in reader.pages:
                try:
                    t = p.extract_text() or ""
                except Exception as e:
                    logger.warning("Failed to extract text from a page: %s", e)
                    t = ""
                text += t + "\n"
    except Exception as e:
        logger.error("Failed to read PDF with PyPDF2: %s", e)
        text = ""
    return text


def extract_page_texts(path: Union[str, Path]) -> List[str]:
    p = Path(path)
    if not p.exists():
        raise PDFQCError(f"PDF file does not exist: {path}")
    texts = []
    if PyPDF2 is not None:
        try:
            with open(path, "rb") as f:
                reader = PyPDF2.PdfReader(f)
                for i, page in enumerate(reader.pages):
                    try:
                        t = page.extract_text() or ""
                    except Exception as page_err:
                        logger.warning("Failed to extract text from page %d using PyPDF2: %s", i + 1, page_err)
                        t = ""
                    texts.append(t)
        except Exception as e:
            logger.error("Failed to extract page texts using PyPDF2: %s", e)
            texts = []
    if not texts and pdfplumber is not None:
        try:
            with pdfplumber.open(path) as pdf:
                for i, page in enumerate(pdf.pages):
                    try:
                        texts.append(page.extract_text() or "")
                    except Exception as page_err:
                        logger.warning("Failed to extract text from page %d using pdfplumber: %s", i + 1, page_err)
                        texts.append("")
        except Exception as e:
            logger.error("Failed to extract page texts using pdfplumber: %s", e)
            texts = []
    return texts


def ocr_pdf_to_text(
    path: Union[str, Path],
    poppler_path: Optional[Union[str, Path]] = None,
    dpi: int = 300,
    pages: Optional[List[int]] = None,
    tesseract_path: Optional[Union[str, Path]] = None
) -> str:
    """
    Convert PDF pages to images and OCR them using pytesseract.
    poppler_path: optional path to poppler binaries (Windows)
    pages: list of 1-based page numbers or None for all
    tesseract_path: optional path to tesseract binary
    """
    if convert_from_path is None or pytesseract is None:
        raise OCRNotFoundError("pdf2image or pytesseract is not installed")
    if tesseract_path:
        tess_p = Path(tesseract_path)
        if not tess_p.exists():
            raise OCRNotFoundError(f"Tesseract path does not exist: {tesseract_path}")
        pytesseract.pytesseract.tesseract_cmd = str(tess_p)
    if poppler_path:
        pop_p = Path(poppler_path)
        if not pop_p.exists():
            raise OCRNotFoundError(f"Poppler path does not exist: {poppler_path}")
    try:
        imgs = convert_from_path(
            path, dpi=dpi, poppler_path=poppler_path, first_page=1, last_page=None
        )
        if pages:
            imgs = [imgs[i - 1] for i in pages if 1 <= i <= len(imgs)]
    except Exception as e:
        logger.error("pdf2image conversion failed: %s", e)
        return ""
    text = ""
    for img in imgs:
        try:
            t = pytesseract.image_to_string(img)
        except Exception as e:
            logger.error("pytesseract OCR failed for image: %s", e)
            t = ""
        text += t + "\n"
    return text


def parse_table_row(line: str) -> Optional[Dict[str, Any]]:
    tokens = line.strip().split()
    if len(tokens) < 4:
        return None
    pos_token = tokens[0]
    if not re.fullmatch(r"\d+(?:\.\d+)?", pos_token):
        return None
    last = tokens[-1].lower()
    length_display = ""
    if last == "mm":
        length_token_raw = tokens[-2]
        desc_tokens = tokens[1:-2]
        length_display = f"{length_token_raw} mm"
    elif last.endswith("mm"):
        length_token_raw = tokens[-1][:-2]
        desc_tokens = tokens[1:-1]
        length_display = tokens[-1]
    else:
        return None
    if not desc_tokens:
        return None
    description = " ".join(desc_tokens).strip()
    if not description:
        return None
    cleaned = re.sub(r"[^\d.,]", "", length_token_raw)
    cleaned = cleaned.replace(",", "")
    if cleaned == "":
        return None
    try:
        length_value = float(cleaned)
    except ValueError:
        return None
    return {
        "pos": pos_token,
        "description": description,
        "length": length_value,
        "length_display": length_display or None,
        "length_options": [length_value],
        "table_page": None,
        "table_anchor": None,
        "quantity": None,
        "quantity_display": None,
        "callout_quantity_text": None,
    }


def normalize_word_token(text: str) -> str:
    return re.sub(r"[^a-z0-9.+-]", "", text.lower())


def _pos_numeric_value(pos):
    if pos is None:
        return None
    pos_str = str(pos).strip()
    if not pos_str:
        return None
    try:
        return float(pos_str)
    except ValueError:
        return None


def _normalize_token_variants(token_variants):
    if not token_variants:
        return []
    if isinstance(token_variants, (list, tuple)) and token_variants and isinstance(token_variants[0], str):
        return [list(token_variants)]
    sequences = []
    for option in token_variants:
        if not option:
            continue
        if isinstance(option, (list, tuple)):
            seq = [str(tok) for tok in option if tok]
            if seq:
                sequences.append(seq)
        elif isinstance(option, str):
            sequences.append([option])
    return sequences


def _match_callout_on_page(tokens, words):
    if not tokens or not words:
        return None
    normalized_words = []
    for word in words:
        norm = normalize_word_token(word.get("text", ""))
        if norm:
            normalized_words.append((word, norm))
    total = len(normalized_words)
    needed = len(tokens)
    for i in range(total - needed + 1):
        if all(normalized_words[i + j][1] == tokens[j] for j in range(needed)):
            matched_words = [normalized_words[i + j][0] for j in range(needed)]
            bbox = {
                "x0": min(w["x0"] for w in matched_words),
                "x1": max(w["x1"] for w in matched_words),
                "top": min(w["top"] for w in matched_words),
                "bottom": max(w["bottom"] for w in matched_words),
            }
            return bbox
    return None


def _numeric_from_text(text):
    if not text:
        return []
    cleaned = text.replace(",", "")
    cleaned = cleaned.replace("\u2212", "-").replace("\u2013", "-").replace("\u2014", "-")
    diameter_symbols = ("Ø", "ø", "φ", "Φ", "⌀", "∅")
    for symbol in diameter_symbols:
        cleaned = cleaned.replace(symbol, " ")
    cleaned = cleaned.replace("×", " ").replace("·", " ").replace("*", " ")
    cleaned = cleaned.replace("X", " ").replace("x", " ")
    cleaned = cleaned.replace("\\", " ").replace("/", " ")
    cleaned = cleaned.replace(";", " ").replace(":", " ")
    cleaned = cleaned.strip("()[]{}<>")
    cleaned = re.sub(r"[A-Za-z]+", " ", cleaned)
    numbers = []
    for match in re.finditer(r"[-+]?\d+(?:\.\d+)?", cleaned):
        try:
            numbers.append(float(match.group(0)))
        except ValueError:
            continue
    return numbers


def is_within_tolerance(
    actual: float,
    expected: float,
    tolerance: float = 0.5,
    mode: Union[ToleranceMode, str] = ToleranceMode.ABSOLUTE
) -> bool:
    """
    Check if actual value is within tolerance of expected value.
    Supports absolute tolerance (e.g. ±0.5 mm) or percentage tolerance (e.g. ±2%).
    """
    mode_str = mode.value if isinstance(mode, ToleranceMode) else str(mode).lower()
    if mode_str == ToleranceMode.PERCENTAGE.value or mode_str == "percentage":
        if expected == 0.0:
            return abs(actual) <= tolerance
        pct_diff = abs(actual - expected) / abs(expected) * 100.0
        return pct_diff <= tolerance
    return abs(actual - expected) <= tolerance


def generate_pos_callout_variants(pos: str) -> List[List[str]]:
    """
    Generate normalized token sequences for matching CAD callouts on drawing sheets.
    Supports common fabrication callout notations:
    - 'POS 1', 'POS-1', 'P1', '#1', 'ITEM 1', 'MK 1', 'MARK 1'
    """
    clean_pos = str(pos).strip().lower()
    if not clean_pos:
        return []

    num_val = _pos_numeric_value(clean_pos)
    num_str = f"{num_val:g}" if num_val is not None else clean_pos

    variants = [
        [clean_pos],
        ["pos", clean_pos],
        [f"pos{clean_pos}"],
        ["item", clean_pos],
        [f"item{clean_pos}"],
        [f"p{clean_pos}"],
        ["mk", clean_pos],
        ["mark", clean_pos],
    ]

    if num_str != clean_pos:
        variants.extend([
            [num_str],
            ["pos", num_str],
            [f"pos{num_str}"],
            ["item", num_str],
            [f"p{num_str}"],
            ["mk", num_str],
        ])

    # Deduplicate while preserving order
    seen = set()
    unique_variants = []
    for seq in variants:
        t_seq = tuple(seq)
        if t_seq not in seen:
            seen.add(t_seq)
            unique_variants.append(seq)

    return unique_variants


def _pick_candidate(
    candidates: List[float],
    expected_length: Optional[float],
    prefer_max: bool = False,
    tolerance: float = 0.5,
    tolerance_mode: Union[ToleranceMode, str] = ToleranceMode.ABSOLUTE
) -> Tuple[Optional[float], str]:
    """
    Return the chosen candidate and selection mode.
    prefer_max=True forces the largest value unless one matches expected_length within tolerance.
    """
    if not candidates:
        return None, "none"
    ordered = sorted(candidates, reverse=True)
    if expected_length is None:
        return ordered[0], "max_in_window"
    if prefer_max:
        for value in ordered:
            if is_within_tolerance(value, expected_length, tolerance, tolerance_mode):
                return value, "match_expected"
        return ordered[0], "max_in_window"
    best = min(candidates, key=lambda v: (abs(v - expected_length), -v))
    return best, "closest_to_expected"



def tokenize(text):
    return [tok for tok in re.split(r"[^a-z0-9]+", text.lower()) if tok]


def contains_subsequence(tokens, subseq):
    if not subseq:
        return False
    n = len(subseq)
    for i in range(len(tokens) - n + 1):
        if tokens[i:i + n] == subseq:
            return True
    return False


def extract_numeric_values(text):
    values = []
    for match in re.finditer(r"\d+(?:[,\s]\d{3})*(?:\.\d+)?", text):
        candidate = match.group(0).replace(" ", "").replace(",", "")
        try:
            values.append(float(candidate))
        except ValueError:
            continue
    return values


UNIT_CONVERSION_TO_MM: Dict[str, float] = {
    "mm": 1.0,
    "millimeter": 1.0,
    "millimeters": 1.0,
    "cm": 10.0,
    "centimeter": 10.0,
    "centimeters": 10.0,
    "m": 1000.0,
    "meter": 1000.0,
    "meters": 1000.0,
    "in": 25.4,
    "inch": 25.4,
    "inches": 25.4,
    '"': 25.4,
    "ft": 304.8,
    "foot": 304.8,
    "feet": 304.8,
    "'": 304.8,
}


def convert_dimension(value: float, from_unit: str, to_unit: str = "mm") -> float:
    """
    Convert a numeric dimension from one unit to another.
    Supported units: mm, cm, m, in, ft. Default target unit is mm.
    """
    src_key = from_unit.strip().lower()
    dst_key = to_unit.strip().lower()

    if src_key not in UNIT_CONVERSION_TO_MM:
        raise ValueError(f"Unsupported source unit: '{from_unit}'")
    if dst_key not in UNIT_CONVERSION_TO_MM:
        raise ValueError(f"Unsupported destination unit: '{to_unit}'")

    val_in_mm = value * UNIT_CONVERSION_TO_MM[src_key]
    converted = val_in_mm / UNIT_CONVERSION_TO_MM[dst_key]
    return round(converted, 4)


def parse_dimension_string(dim_str: str, default_unit: str = "mm") -> Tuple[Optional[float], Optional[str]]:
    """
    Parse a dimension string that may include units or fractional inches.
    Examples:
        '150 mm' -> (150.0, '150 mm')
        '1.5 m' -> (1500.0, '1.5 m')
        '1/2"' -> (12.7, '1/2"')
        '2-1/2"' -> (63.5, '2-1/2"')
        '3 in' -> (76.2, '3 in')
    Returns:
        (value_in_mm, raw_display_string) or (None, None) if parsing fails.
    """
    if not dim_str:
        return None, None
    s = dim_str.strip()

    # Pattern for fractional inches like 2-1/2", 2 1/2", 1/2", 3/4 in
    fraction_pattern = r'^(?:(\d+)[-\s]+)?(\d+)/(\d+)\s*(["\']|in|inch|inches|ft|mm|cm|m)?$'
    frac_match = re.match(fraction_pattern, s, re.IGNORECASE)
    if frac_match:
        whole_str, num_str, denom_str, unit_str = frac_match.groups()
        whole = float(whole_str) if whole_str else 0.0
        denom = float(denom_str)
        if denom == 0:
            return None, None
        fraction_val = float(num_str) / denom
        total_val = whole + fraction_val
        unit = unit_str.lower() if unit_str else "in"
        val_mm = convert_dimension(total_val, unit, "mm")
        return val_mm, s

    # Standard decimal pattern: '150.5 mm', '2.5 in', '100'
    decimal_pattern = r'^([-+]?\d+(?:[,\s]\d{3})*(?:\.\d+)?)\s*([a-zA-Z"\'°]*)$'
    dec_match = re.match(decimal_pattern, s)
    if dec_match:
        num_part, unit_part = dec_match.groups()
        cleaned_num = num_part.replace(",", "").replace(" ", "")
        try:
            val = float(cleaned_num)
        except ValueError:
            return None, None
        unit = unit_part.lower() if unit_part else default_unit.lower()
        if unit in UNIT_CONVERSION_TO_MM:
            val_mm = convert_dimension(val, unit, "mm")
            return val_mm, s
        elif not unit:
            return val, s

    return None, None


def format_length(value: float) -> str:
    text = f"{value:.3f}".rstrip("0").rstrip(".")
    return f"{text} mm"



SECTION_KEYWORDS = ["PROFILES", "PROFILE", "PLATES", "PLATE", "PINS", "PIN"]
MEASUREMENT_PRIORITY = [
    (("LENGTH", "LENGTH (MM)", "LENGTHMM"), "length"),
    (("SIZE", "DIMENSION", "DIMENSIONS"), "size"),
]
QUANTITY_KEYWORDS = ("ITEM QTY", "ITEMQTY", "ITEM_QTY", "QTY", "QUANTITY", "Q'TY")


def _normalize_header_token(cell):
    upper = (cell or "").upper()
    compact = re.sub(r"[^A-Z0-9]+", "", upper)
    return upper, compact


def _header_matches(cell, keywords):
    upper, compact = _normalize_header_token(cell)
    for key in keywords:
        key_upper = key.upper()
        key_compact = re.sub(r"[^A-Z0-9]+", "", key_upper)
        if key_upper in upper or key_compact in compact:
            return True
    return False


def _find_header_index(header_row, keywords):
    for idx, cell in enumerate(header_row):
        if _header_matches(cell, keywords):
            return idx
    return None


def _find_measurement_index(header_row):
    for keywords, measure_type in MEASUREMENT_PRIORITY:
        idx = _find_header_index(header_row, keywords)
        if idx is not None:
            return idx, measure_type
    return None, None


def _parse_row_description(cells, desc_idx, measure_idx):
    desc_parts = []
    for idx in range(desc_idx, measure_idx):
        if idx == desc_idx:
            desc_parts.append((cells[idx] or "").strip())
        else:
            part = (cells[idx] or "").strip()
            if part:
                desc_parts.append(part)
    if not desc_parts:
        return None
    return " ".join(desc_parts)


def _parse_row_thickness(cells, thickness_idx):
    if thickness_idx is None or thickness_idx >= len(cells):
        return None, None
    thickness_token_raw = (cells[thickness_idx] or "").strip()
    if not thickness_token_raw:
        return None, None
    thickness_display = thickness_token_raw
    thickness_value = None
    thickness_numbers = re.findall(
        r"[-+]?\d+(?:\.\d+)?", thickness_token_raw.replace(",", "")
    )
    if thickness_numbers:
        try:
            thickness_value = abs(float(thickness_numbers[0]))
        except ValueError:
            thickness_value = None
    return thickness_value, thickness_display


def _parse_row_quantity(cells, quantity_idx):
    if quantity_idx is None or quantity_idx >= len(cells):
        return None, None
    quantity_raw = (cells[quantity_idx] or "").strip()
    if not quantity_raw:
        return None, None
    quantity_display = quantity_raw
    quantity_value = None
    qty_numbers = re.findall(
        r"[-+]?\d+(?:\.\d+)?", quantity_raw.replace(",", "")
    )
    if qty_numbers:
        try:
            quantity_value = float(qty_numbers[0])
        except ValueError:
            quantity_value = None
    return quantity_value, quantity_display


def _generate_row_key(pos_value, description, length_options, measure_type, thickness_value, quantity_value, quantity_text):
    length_key = tuple(round(v, 6) for v in length_options)
    thickness_key = round(thickness_value, 6) if thickness_value is not None else None
    if quantity_value is not None:
        quantity_key = round(quantity_value, 6)
    elif quantity_text:
        quantity_key = quantity_text.strip().lower()
    else:
        quantity_key = None
    return (pos_value, description, length_key, measure_type, thickness_key, quantity_key)


def extract_rows_with_plumber(path):
    if pdfplumber is None:
        return [], [], []
    rows = []
    snippets = []
    words_by_page = []
    seen = set()
    table_counter = 0

    try:
        with pdfplumber.open(path) as pdf:
            for page_idx, page in enumerate(pdf.pages, start=1):
                page_words = page.extract_words(
                    x_tolerance=1.5, y_tolerance=1.5, keep_blank_chars=False, use_text_flow=True
                ) or []
                words_by_page.append(page_words)
                page_text_upper = (page.extract_text() or "").upper()
                has_section_word = any(word in page_text_upper for word in SECTION_KEYWORDS)
                tables = page.extract_tables()
                if not tables:
                    continue

                # index words by their text for this page to find POS cell bboxes
                words_by_text = {}
                for w in page_words:
                    t = (w.get("text") or "").strip()
                    if t:
                        words_by_text.setdefault(t, []).append(w)

                for table in tables:
                    if not table:
                        continue
                    normalized = [[(cell or "").strip() for cell in row] for row in table]
                    is_target_table = any(
                        _header_matches(cell, SECTION_KEYWORDS)
                        for row in normalized[:2]
                        for cell in row
                    )
                    if not is_target_table and not has_section_word:
                        continue
                    header_row = None
                    pos_idx = desc_idx = measure_idx = None
                    measure_type = None
                    thickness_idx = None
                    quantity_idx = None
                    table_title = None
                    for candidate in normalized:
                        candidate_pos = _find_header_index(candidate, ("POS",))
                        candidate_desc = _find_header_index(candidate, ("DESCRIPTION", "DESC"))
                        candidate_measure_idx, candidate_measure_type = _find_measurement_index(candidate)
                        if (
                            candidate_pos is not None
                            and candidate_desc is not None
                            and candidate_measure_idx is not None
                        ):
                            header_row = candidate
                            pos_idx = candidate_pos
                            desc_idx = candidate_desc
                            measure_idx = candidate_measure_idx
                            measure_type = candidate_measure_type
                            thickness_idx = _find_header_index(candidate, ("THICKNESS", "THK", "THICK"))
                            quantity_idx = _find_header_index(candidate, QUANTITY_KEYWORDS)
                            break
                    if header_row is None:
                        continue
                    if measure_idx is None or measure_type is None:
                        continue
                    header_pos = normalized.index(header_row)
                    data_rows = normalized[header_pos + 1 :]
                    if pos_idx is None or desc_idx is None:
                        continue
                    if measure_idx <= desc_idx or measure_idx <= pos_idx:
                        continue
                    # derive table label/title
                    if table_title is None:
                        for label_row in normalized[:header_pos]:
                            candidates = [cell for cell in label_row if cell]
                            if len(candidates) == 1:
                                cand_text = candidates[0].strip()
                                if len(cand_text) >= 3:
                                    table_title = cand_text
                    table_counter += 1
                    table_label = table_title or f"Table {table_counter} (page {page_idx})"
                    for raw_row in data_rows:
                        if not raw_row:
                            continue
                        cells = raw_row
                        if not any(cells):
                            continue
                        pos_value_raw = (cells[pos_idx] or "").strip()
                        if not re.fullmatch(r"\d+(?:\.\d+)?", pos_value_raw.replace(" ", "")):
                            continue
                        # description
                        description = _parse_row_description(cells, desc_idx, measure_idx)
                        if not description:
                            continue
                        # measurement
                        measure_token_raw = (cells[measure_idx] or "").strip()
                        if not measure_token_raw:
                            continue
                        length_display = measure_token_raw
                        length_value = None
                        length_options = []
                        if measure_type == "length":
                            cleaned = re.sub(r"[^\d.,+-]", "", measure_token_raw).replace(",", "")
                            if cleaned == "":
                                continue
                            try:
                                length_value = float(cleaned)
                            except ValueError:
                                continue
                            length_options = [length_value]
                            if not measure_token_raw.lower().strip().endswith("mm"):
                                length_display = f"{measure_token_raw} mm"
                        elif measure_type == "size":
                            number_strings = re.findall(r"\d+(?:\.\d+)?", measure_token_raw.replace(",", ""))
                            numeric_values = []
                            for token in number_strings:
                                try:
                                    numeric_values.append(float(token))
                                except ValueError:
                                    continue
                            if not numeric_values:
                                continue
                            length_value = numeric_values[0]
                            length_options = numeric_values
                        if length_value is None:
                            continue
                        if not length_options:
                            length_options = [length_value]
                        # quantity
                        quantity_value, quantity_display = _parse_row_quantity(cells, quantity_idx)
                        quantity_text = quantity_display
                        # thickness
                        thickness_value, thickness_display = _parse_row_thickness(cells, thickness_idx)
                        pos_value = pos_value_raw.replace(" ", "")
                        key = _generate_row_key(
                            pos_value, description, length_options, measure_type, thickness_value, quantity_value, quantity_text
                        )
                        if key in seen:
                            continue
                        seen.add(key)

                        # anchor bbox for the POS cell (retained for potential overlays)
                        table_anchor = None
                        candidates = words_by_text.get(pos_value_raw) or words_by_text.get(pos_value)
                        if candidates:
                            cand = sorted(candidates, key=lambda w: (w.get("x0", 0), w.get("top", 0)))[0]
                            table_anchor = {
                                "x0": float(cand.get("x0", 0.0)),
                                "x1": float(cand.get("x1", 0.0)),
                                "top": float(cand.get("top", 0.0)),
                                "bottom": float(cand.get("bottom", 0.0)),
                            }

                        rows.append({
                            "pos": pos_value,
                            "description": description,
                            "length": length_value,
                            "length_display": length_display or None,
                            "length_options": length_options,
                            "table_id": table_counter,
                            "table_label": table_label,
                            "quantity": quantity_value,
                            "quantity_display": quantity_display or None,
                            "callout_quantity_text": quantity_text or None,
                            "thickness": thickness_value,
                            "thickness_display": thickness_display or None,
                            "table_page": page_idx,
                            "table_anchor": table_anchor,
                        })
                        snippet_text = " ".join(c for c in cells if c)
                        if snippet_text:
                            snippets.append((page_idx, snippet_text))
    except Exception:
        return [], [], []
    return rows, snippets, words_by_page


def remove_table_snippets_from_pages(page_texts, snippets):
    if not page_texts or not snippets:
        return page_texts
    page_map = {}
    for page_idx, snippet in snippets:
        if not snippet:
            continue
        page_map.setdefault(page_idx, []).append(snippet.lower())
    cleaned = []
    for idx, text in enumerate(page_texts, start=1):
        lowers = page_map.get(idx)
        if not lowers:
            cleaned.append(text)
            continue
        lines = text.splitlines()
        kept = []
        for line in lines:
            lower = line.lower()
            if any(snippet in lower for snippet in lowers):
                continue
            kept.append(line)
        cleaned.append("\n".join(kept))
    return cleaned


def export_to_csv(results: List[Dict[str, Any]], columns: Optional[List[str]] = None) -> str:
    import io
    import csv
    
    output = io.StringIO()
    writer = csv.writer(output, lineterminator='\n')
    
    default_headers = {
        "pos": "POS",
        "description": "Description",
        "status": "Status",
        "quantity": "BOM Qty",
        "length_bom": "BOM Length",
        "length_dwg": "DWG Length",
        "length_match": "Length Match",
        "thickness_bom": "BOM Thickness",
        "thickness_dwg": "DWG Thickness",
        "thickness_match": "Thickness Match",
        "details": "Details",
    }
    
    if columns is None:
        columns = list(default_headers.keys())
        
    headers = [default_headers.get(col, col.capitalize()) for col in columns]
    writer.writerow(headers)
    
    for r in results:
        row_data = []
        for col in columns:
            if col == "pos":
                row_data.append(r.get("pos", ""))
            elif col == "description":
                row_data.append(r.get("description", ""))
            elif col == "status":
                row_data.append(r.get("status", ""))
            elif col == "quantity":
                row_data.append(r.get("quantity_display", r.get("quantity", "") or ""))
            elif col == "length_bom":
                row_data.append(r.get("length_display", r.get("length", "") or ""))
            elif col == "length_dwg":
                row_data.append("N/A" if not r.get("length_found") else r.get("drawing_length", ""))
            elif col == "length_match":
                row_data.append("Yes" if r.get("length_match") else "No")
            elif col == "thickness_bom":
                row_data.append(r.get("thickness_display", r.get("thickness", "") or ""))
            elif col == "thickness_dwg":
                row_data.append("N/A" if not r.get("thickness_found") else r.get("drawing_thickness", ""))
            elif col == "thickness_match":
                row_data.append("Yes" if r.get("thickness_match") else "No")
            elif col == "details":
                row_data.append(r.get("details", ""))
            else:
                row_data.append(r.get(col, ""))
        writer.writerow(row_data)
        
    return output.getvalue()


def export_to_json(results: List[Dict[str, Any]]) -> str:
    import json
    return json.dumps(results, indent=4)


def export_to_html(results: List[Dict[str, Any]], title: str = "BOM Quality Control Audit Report") -> str:
    """
    Generate a self-contained, beautifully styled HTML audit report.
    Includes overall metrics, status breakdown, and color-coded table rows.
    """
    import html
    from datetime import datetime

    summary = CheckSummary.from_results(results)
    timestamp_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    badge_class = "badge-success" if summary.pass_rate >= 80 else ("badge-warning" if summary.pass_rate >= 50 else "badge-danger")

    rows_html = []
    for r in results:
        status = html.escape(str(r.get("status", "FAIL")))
        pos = html.escape(str(r.get("pos", "")))
        desc = html.escape(str(r.get("description", "")))
        qty = html.escape(str(r.get("quantity_display", r.get("quantity", "")) or "-"))
        len_bom = html.escape(str(r.get("length_display", r.get("length", "")) or "-"))
        len_dwg = html.escape(str(r.get("drawing_length", "N/A") if r.get("length_found") else "N/A"))
        len_match = '<span class="status-yes">Yes</span>' if r.get("length_match") else '<span class="status-no">No</span>'
        thk_bom = html.escape(str(r.get("thickness_display", r.get("thickness", "")) or "-"))
        thk_dwg = html.escape(str(r.get("drawing_thickness", "N/A") if r.get("thickness_found") else "N/A"))
        thk_match = '<span class="status-yes">Yes</span>' if r.get("thickness_match") else '<span class="status-no">No</span>'
        details = html.escape(str(r.get("details", "")))

        status_class = "row-pass" if status == "PASS" else ("row-warn" if status == "WARNING" else "row-fail")
        badge_style = "badge-success" if status == "PASS" else ("badge-warning" if status == "WARNING" else "badge-danger")

        rows_html.append(f"""
            <tr class="{status_class}">
                <td><strong>{pos}</strong></td>
                <td>{desc}</td>
                <td><span class="badge {badge_style}">{status}</span></td>
                <td>{qty}</td>
                <td>{len_bom}</td>
                <td>{len_dwg}</td>
                <td>{len_match}</td>
                <td>{thk_bom}</td>
                <td>{thk_dwg}</td>
                <td>{thk_match}</td>
                <td><small>{details}</small></td>
            </tr>
        """)

    table_body = "\n".join(rows_html)

    html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{html.escape(title)}</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
            background-color: #f4f6f9;
            color: #2d3748;
            margin: 0;
            padding: 24px;
        }}
        .container {{
            max-width: 1200px;
            margin: 0 auto;
            background: #ffffff;
            border-radius: 8px;
            box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1);
            overflow: hidden;
            padding: 32px;
        }}
        h1 {{
            margin-top: 0;
            color: #1a202c;
            border-bottom: 2px solid #e2e8f0;
            padding-bottom: 12px;
        }}
        .meta {{
            color: #718096;
            font-size: 0.9rem;
            margin-bottom: 24px;
        }}
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(180px, 1fr));
            gap: 16px;
            margin-bottom: 32px;
        }}
        .stat-card {{
            background: #f7fafc;
            border: 1px solid #e2e8f0;
            border-radius: 6px;
            padding: 16px;
            text-align: center;
        }}
        .stat-value {{
            font-size: 1.8rem;
            font-weight: bold;
            color: #2b6cb0;
        }}
        .stat-label {{
            font-size: 0.85rem;
            color: #4a5568;
            text-transform: uppercase;
            letter-spacing: 0.05em;
        }}
        table {{
            width: 100%;
            border-collapse: collapse;
            font-size: 0.95rem;
        }}
        th, td {{
            padding: 12px 14px;
            text-align: left;
            border-bottom: 1px solid #e2e8f0;
        }}
        th {{
            background-color: #edf2f7;
            color: #4a5568;
            font-weight: 600;
        }}
        tr:hover {{
            background-color: #f7fafc;
        }}
        .row-pass {{ background-color: #f0fff4; }}
        .row-fail {{ background-color: #fff5f5; }}
        .badge {{
            display: inline-block;
            padding: 4px 8px;
            border-radius: 4px;
            font-size: 0.8rem;
            font-weight: 600;
        }}
        .badge-success {{ background-color: #c6f6d5; color: #22543d; }}
        .badge-warning {{ background-color: #feebc8; color: #744210; }}
        .badge-danger {{ background-color: #fed7d7; color: #742a2a; }}
        .status-yes {{ color: #22543d; font-weight: bold; }}
        .status-no {{ color: #742a2a; font-weight: bold; }}
        footer {{
            margin-top: 32px;
            font-size: 0.85rem;
            color: #a0aec0;
            text-align: center;
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>{html.escape(title)}</h1>
        <div class="meta">Generated: {timestamp_str} | Tool: PDF Drawing Checker v1.2</div>
        <div class="stats-grid">
            <div class="stat-card">
                <div class="stat-value">{summary.total_items}</div>
                <div class="stat-label">Total Items</div>
            </div>
            <div class="stat-card">
                <div class="stat-value" style="color: #2f855a;">{summary.passed}</div>
                <div class="stat-label">Passed</div>
            </div>
            <div class="stat-card">
                <div class="stat-value" style="color: #c53030;">{summary.failed}</div>
                <div class="stat-label">Failed</div>
            </div>
            <div class="stat-card">
                <div class="stat-value {badge_class}">{summary.pass_rate}%</div>
                <div class="stat-label">Pass Rate</div>
            </div>
        </div>
        <table>
            <thead>
                <tr>
                    <th>POS</th>
                    <th>Description</th>
                    <th>Status</th>
                    <th>Qty</th>
                    <th>BOM Length</th>
                    <th>DWG Length</th>
                    <th>Length Match</th>
                    <th>BOM Thk</th>
                    <th>DWG Thk</th>
                    <th>Thk Match</th>
                    <th>Details</th>
                </tr>
            </thead>
            <tbody>
                {table_body}
            </tbody>
        </table>
        <footer>
            Automated QC Report &bull; CAD Quality Assurance
        </footer>
    </div>
</body>
</html>"""
    return html_content


