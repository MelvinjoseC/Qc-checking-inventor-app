import re
import sys
import json
import logging
from pathlib import Path

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


DEFAULT_CONFIG = {
    "tolerance": 0.5,
    "default_dpi": 300,
    "poppler_path": "",
    "tesseract_path": ""
}

def validate_config(config):
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


def load_config(path='config.json'):
    try:
        p = Path(path)
        if p.exists():
            with open(p, 'r', encoding='utf-8') as f:
                config = json.load(f)
                return validate_config(config)
    except Exception as e:
        logger.warning("Failed to load config, using defaults: %s", e)
    return DEFAULT_CONFIG.copy()

def save_config(config, path='config.json'):
    try:
        p = Path(path)
        with open(p, 'w', encoding='utf-8') as f:
            json.dump(config, f, indent=4)
        return True
    except Exception as e:
        logger.error("Failed to save config to %s: %s", path, e)
        return False


def load_spellcheck_allowlist(path='spellcheck_allowlist.txt'):
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


def extract_text_from_pdf(path):
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


def extract_page_texts(path):
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


def ocr_pdf_to_text(path, poppler_path=None, dpi=300, pages=None, tesseract_path=None):
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


def parse_table_row(line):
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


def normalize_word_token(text):
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


def _pick_candidate(candidates, expected_length, prefer_max=False, tolerance=0.5):
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
            if abs(value - expected_length) <= tolerance:
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


def format_length(value):
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


def export_to_csv(results, columns=None):
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


def export_to_json(results):
    import json
    return json.dumps(results, indent=4)

