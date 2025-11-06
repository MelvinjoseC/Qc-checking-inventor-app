#!/usr/bin/env python3
"""
PDF Drawing Checker
-------------------

Load a fabrication drawing PDF, read the BOM/table entries (POS, DESCRIPTION, LENGTH),
and verify that each row has a matching callout and matching length elsewhere in the drawing.
The app shows a PASS/FAIL result per row and an overall status.


Dependencies (install before running):
  pip install PyPDF2 pdfplumber pdf2image pytesseract pillow pyspellchecker

System requirements for OCR fallback:
  - Tesseract OCR installed (https://github.com/tesseract-ocr/tesseract) and on PATH.
  - Poppler utilities (for pdf2image). On Windows download Poppler and set PATH or pick the folder when prompted.
"""

import os
import re
import sys
import copy
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from pathlib import Path
import threading
import traceback

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

try:
    from spellchecker import SpellChecker
except Exception:
    SpellChecker = None

# --- Helpers: shared resources & text extraction from PDF ---
def resource_path(relative_path):
    """
    Resolve a bundled resource path that works for both source execution and PyInstaller builds.
    """
    base_path = getattr(sys, "_MEIPASS", None)
    if base_path:
        return Path(base_path) / relative_path
    return Path(__file__).resolve().parent / relative_path


def extract_text_from_pdf(path):
    """Try to extract text with PyPDF2. Returns combined text of all pages (may be empty)."""
    text = ""
    if PyPDF2 is None:
        return text
    try:
        with open(path, "rb") as f:
            reader = PyPDF2.PdfReader(f)
            for p in reader.pages:
                try:
                    t = p.extract_text() or ""
                except Exception:
                    t = ""
                text += t + "\n"
    except Exception:
        text = ""
    return text


def extract_page_texts(path):
    texts = []
    if PyPDF2 is not None:
        try:
            with open(path, "rb") as f:
                reader = PyPDF2.PdfReader(f)
                for page in reader.pages:
                    try:
                        t = page.extract_text() or ""
                    except Exception:
                        t = ""
                    texts.append(t)
        except Exception:
            texts = []
    if not texts and pdfplumber is not None:
        try:
            with pdfplumber.open(path) as pdf:
                texts = [(page.extract_text() or "") for page in pdf.pages]
        except Exception:
            texts = []
    return texts


def ocr_pdf_to_text(path, poppler_path=None, dpi=300, pages=None):
    """
    Convert PDF pages to images and OCR them using pytesseract.
    poppler_path: optional path to poppler binaries (Windows)
    pages: list of 1-based page numbers or None for all
    """
    if convert_from_path is None or pytesseract is None:
        return ""
    try:
        imgs = convert_from_path(
            path, dpi=dpi, poppler_path=poppler_path, first_page=1, last_page=None
        )
        if pages:
            imgs = [imgs[i - 1] for i in pages if 1 <= i <= len(imgs)]
    except Exception as e:
        print("pdf2image conversion failed:", e)
        return ""
    text = ""
    for img in imgs:
        try:
            t = pytesseract.image_to_string(img)
        except Exception:
            t = ""
        text += t + "\n"
    return text


SPELLCHECK_ALLOWLIST = {
    "galv",
    "gal",
    "rhs",
    "lhs",
    "chs",
    "pfc",
    "thk",
    "hdg",
    "qty",
    "stl",
    "ss",
    "ms",
}


# --- GUI app ---
class PDFQCApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("PDF Drawing Checker")
        self.geometry("1160x640")
        self.configure(bg="#eef1f8")
        self.palette = {
            "bg": "#eef1f8",
            "surface": "#ffffff",
            "overlay": "#ffffff",
            "overlay_dim": "#ffffff",
            "accent": "#4f6bed",
            "accent_hover": "#6c82ff",
            "accent_active": "#374ecc",
            "muted": "#5f6c7b",
            "text": "#20242c",
            "border": "#d9deea",
            "success_bg": "#e5f7ef",
            "success_fg": "#217346",
            "error_bg": "#fdebea",
            "error_fg": "#c0392b",
        }
        self._setup_style()

        self.pdf_path = None
        self.poppler_path = None  # set if OCR needs poppler
        self.drawing_text = ""
        self.page_texts = []
        self.page_words = []
        self.current_file_display = ""
        self.history_entries = []
        self.pos_analysis = {}
        self.spell_checker = None
        self.spell_issues = {"rows": {}, "pages": {}}
        self._summary_base_parts = []
        self._latest_summary_text = ""
        self._pending_history = None
        self._spellcheck_thread = None
        self._active_spellcheck_job = 0
        self._spellcache = {}
        self._spell_last_completed_job = 0
        self._row_tree_items = {}
        self.spell_tab = None
        self.spell_tree = None
        self._latest_results = []
        self._analysis_thread = None
        self._analysis_job = 0
        self._analysis_in_progress = False
        self.table_anchors_by_page = {}

        self.loading_message_var = tk.StringVar(value="")
        self.loading_overlay = tk.Frame(self, bg=self.palette["overlay"], bd=0, highlightthickness=0)
        dim_color = self.palette.get("overlay_dim", "#ffffff")
        self._overlay_canvas = tk.Canvas(
            self.loading_overlay,
            bg=dim_color,
            highlightthickness=0,
            bd=0,
        )
        self._overlay_canvas.place(relx=0, rely=0, relwidth=1, relheight=1)

        def _resize_overlay(_event=None):
            self._overlay_canvas.delete("dim")
            width = self._overlay_canvas.winfo_width()
            height = self._overlay_canvas.winfo_height()
            if width > 0 and height > 0:
                self._overlay_canvas.create_rectangle(
                    0,
                    0,
                    width,
                    height,
                    fill=dim_color,
                    outline="",
                    stipple="gray50",
                    tags="dim",
                )

        self._overlay_canvas.bind("<Configure>", _resize_overlay)

        overlay_inner = ttk.Frame(self.loading_overlay, padding=20, style="Overlay.TFrame")
        overlay_inner.place(relx=0.5, rely=0.5, anchor="center")
        overlay_inner.lift()
        ttk.Label(overlay_inner, textvariable=self.loading_message_var, style="Overlay.TLabel").pack(pady=(0, 10))
        self.loading_overlay.place_forget()
        self.loading_overlay.place_forget()
        top = ttk.Frame(self, style="App.TFrame")
        top.pack(fill="x", padx=16, pady=(16, 12))
        self.loading_animation_job = None
        self.loading_animation_phase = 0

        self.upload_button = ttk.Button(
            top, text="Upload PDF and Check", style="Primary.TButton", command=self.select_pdf
        )
        self.upload_button.pack(side="left")

        logo_path = resource_path("download.png")
        if logo_path.exists():
            logo_image = tk.PhotoImage(file=str(logo_path))
            logo_image = logo_image.subsample(3, 3)
            self.logo_image = logo_image
            ttk.Label(top, image=logo_image, style="AppLogo.TLabel").pack(side="right", padx=(0, 16))

        history_container = ttk.Frame(top, style="Card.TFrame", padding=14)
        history_container.pack(side="left", padx=24)
        ttk.Label(history_container, text="Recent files", style="SectionTitle.TLabel").pack(anchor="w")
        self.current_file_var = tk.StringVar(value="No file loaded")
        ttk.Label(history_container, textvariable=self.current_file_var, style="CardMuted.TLabel").pack(anchor="w", pady=(4, 8))
        self.history_buttons_frame = ttk.Frame(history_container, style="Card.TFrame")
        self.history_buttons_frame.pack(anchor="w", fill="x", pady=(6, 0))
        self._update_history_ui()

        columns = (
            "pos",
            "description",
            "quantity",
            "length_bom",
            "length_dwg",
            "thickness_bom",
            "thickness_dwg",
        )
        tree_frame = ttk.Frame(self, style="App.TFrame")
        tree_frame.pack(fill="both", expand=True, padx=16, pady=(0, 16))

        self.table_columns = columns
        self.table_headings = {
            "pos": "POS",
            "description": "Description",
            "quantity": "Qty",
            "length_bom": "Length (BOM)",
            "length_dwg": "Length (DWG)",
            "thickness_bom": "Thickness (BOM)",
            "thickness_dwg": "Thickness (DWG)",
        }
        self.table_column_widths = {
            "pos": 70,
            "description": 250,
            "quantity": 70,
            "length_bom": 160,
            "length_dwg": 160,
            "thickness_bom": 160,
            "thickness_dwg": 160,
        }

        self.table_notebook = ttk.Notebook(tree_frame, style="Modern.TNotebook")
        self.table_notebook.pack(fill="both", expand=True)
        self.trees = {}

        self.summary_var = tk.StringVar(value="Load a PDF drawing to run the table check.")
        self.spell_button = None
        self.source_var = tk.StringVar(value="")

        footer = ttk.Frame(self, style="Footer.TFrame", padding=(12, 6))
        footer.pack(fill="x", padx=16, pady=(0, 12))
        footer.columnconfigure(0, weight=1)
        ttk.Label(footer, text="© 2025 All rights reserved | Powered by Fusieengineers.Ai", style="Footer.TLabel").grid(row=0, column=0, sticky="n")

    def _setup_style(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        self.option_add("*Font", ("Segoe UI", 10))
        self.option_add("*TButton.Padding", (14, 8))
        self.option_add("*TEntry.Padding", (6, 4))
        palette = self.palette
        style.configure("App.TFrame", background=palette["bg"])
        style.configure("Card.TFrame", background=palette["surface"], relief="flat", borderwidth=0)
        style.configure("Overlay.TFrame", background=palette["overlay"])
        style.configure("AppLogo.TLabel", background=palette["bg"])
        style.configure("Overlay.TLabel", background=palette["overlay"], foreground=palette["muted"], font=("Segoe UI", 11))
        style.configure("SummaryTitle.TLabel", background=palette["surface"], foreground=palette["text"], font=("Segoe UI Semibold", 11))
        style.configure("SummaryValue.TLabel", background=palette["surface"], foreground=palette["muted"], font=("Segoe UI", 10))
        style.configure("Muted.TLabel", background=palette["bg"], foreground=palette["muted"], font=("Segoe UI", 9))
        style.configure("CardMuted.TLabel", background=palette["surface"], foreground=palette["muted"], font=("Segoe UI", 9))
        style.configure("SectionTitle.TLabel", background=palette["surface"], foreground=palette["text"], font=("Segoe UI Semibold", 11))
        style.configure("Result.TLabel", background=palette["surface"], foreground=palette["accent"], font=("Segoe UI Semibold", 10))
        style.configure("TEntry", fieldbackground="#ffffff", foreground=palette["text"])
        style.configure("Primary.TButton", background=palette["accent"], foreground="#ffffff", font=("Segoe UI Semibold", 10), borderwidth=0)
        style.map(
            "Primary.TButton",
            background=[("pressed", palette["accent_active"]), ("active", palette["accent_hover"])],
            foreground=[("disabled", palette["muted"])],
        )
        style.configure(
            "History.TButton",
            background=palette["surface"],
            foreground=palette["accent"],
            font=("Segoe UI", 9),
            borderwidth=0,
            padding=4,
        )
        style.configure(
            "HistorySelected.TButton",
            background=palette["accent"],
            foreground="#ffffff",
            font=("Segoe UI Semibold", 9),
            borderwidth=0,
            padding=4,
        )
        style.map(
            "History.TButton",
            background=[
                ("active", palette["accent_hover"]),
                ("pressed", palette["accent_active"]),
                ("!disabled", palette["surface"]),
                ("selected", palette["accent"]),
                ("disabled", palette["surface"]),
            ],
            foreground=[
                ("active", "#ffffff"),
                ("pressed", "#ffffff"),
                ("selected", "#ffffff"),
                ("disabled", palette["muted"]),
            ],
            relief=[("selected", "solid")],
            bordercolor=[("selected", palette["accent_active"])],
        )
        style.configure("Secondary.TButton", background=palette["surface"], foreground=palette["accent"], borderwidth=1, relief="flat", font=("Segoe UI", 10))
        style.map(
            "Secondary.TButton",
            background=[("pressed", palette["border"]), ("active", palette["border"])],
            foreground=[("disabled", palette["muted"]), ("active", palette["accent_active"])],
            bordercolor=[("active", palette["accent"])],
        )
        style.configure("Modern.TNotebook", background=palette["bg"], borderwidth=0, padding=(2, 6))
        style.configure("Modern.TNotebook.Tab", background=palette["surface"], foreground=palette["muted"], padding=(18, 10), font=("Segoe UI Semibold", 9), borderwidth=0)
        style.map(
            "Modern.TNotebook.Tab",
            background=[("selected", palette["accent"]), ("active", palette["accent_hover"])],
            foreground=[("selected", "#ffffff"), ("active", "#ffffff")],
        )
        style.configure("Modern.Treeview", background=palette["surface"], fieldbackground=palette["surface"], bordercolor=palette["border"], borderwidth=0, font=("Segoe UI", 10), rowheight=30)
        style.configure("Modern.Treeview.Heading", background=palette["bg"], foreground=palette["muted"], relief="flat", font=("Segoe UI Semibold", 10), padding=(6, 8))
        style.map("Modern.Treeview", background=[("selected", "#dce4ff")], foreground=[("selected", palette["text"])])
        style.map("Modern.Treeview.Heading", background=[("active", palette["accent"])], foreground=[("active", "#ffffff")])
        style.configure("Loading.Horizontal.TProgressbar", background=palette["accent"], troughcolor=palette["surface"], bordercolor=palette["surface"])
        style.configure("Footer.TFrame", background=palette["bg"])
        style.configure("Footer.TLabel", background=palette["bg"], foreground=palette["accent_active"], font=("Segoe UI Semibold", 9))

    def select_pdf(self):
        path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")], title="Select PDF drawing")
        if not path:
            return
        self.pdf_path = path
        self.summary_var.set(f"Analyzing {Path(path).name}...")
        self.update_idletasks()
        self.show_loading(f"Loading {Path(path).name} ...")
        try:
            self.process_pdf(path)
        except Exception:
            self.hide_loading()
            raise

    def process_pdf(self, path):
        if self._analysis_in_progress:
            messagebox.showinfo("Processing", "Please wait for the current analysis to finish.")
            return
        text, source = self.get_pdf_text(path)
        if not text or not text.strip():
            messagebox.showerror(
                "Text extraction failed",
                "Could not read text from the PDF. Ensure the drawing contains selectable text or install OCR dependencies.",
            )
            self.summary_var.set("Failed to read the PDF.")
            self.source_var.set("")
            self.current_file_display = ""
            self.clear_tables()
            self.hide_loading()
            return

        self._analysis_job += 1
        job_id = self._analysis_job
        self._analysis_in_progress = True
        display_name = Path(path).name
        self.current_file_display = display_name
        self.source_var.set(f"File: {display_name}")
        self.summary_var.set(f"Analyzing {display_name}...")
        self.show_loading(f"Analyzing {display_name} ...")
        self._update_upload_button_state()

        worker = threading.Thread(
            target=self._process_pdf_worker,
            args=(job_id, path, text, source),
            daemon=True,
        )
        worker.start()
        self._analysis_thread = worker

    def _process_pdf_worker(self, job_id, path, text, source):
        try:
            page_texts_raw = extract_page_texts(path)
            default_page_texts = page_texts_raw if page_texts_raw else ([text] if text else [])
            rows, table_snippets, page_words = extract_rows_with_plumber(path)
            used_plumber_rows = False
            drawing_text = text
            if rows:
                used_plumber_rows = True
                cleaned_pages = remove_table_snippets_from_pages(default_page_texts, table_snippets)
                if not cleaned_pages:
                    cleaned_pages = default_page_texts
                page_texts_clean = cleaned_pages
                drawing_text = "\n".join(cleaned_pages)
            else:
                rows, drawing_text = self.extract_table_rows(text)
                page_texts_clean = default_page_texts if default_page_texts else [drawing_text]
                if not rows:
                    payload = {
                        "status": "no_rows",
                        "message": "Couldn't find any POS/DESCRIPTION/LENGTH rows in this PDF.",
                        "source": source,
                    }
                    self.after(0, lambda: self._on_pdf_processed(job_id, payload))
                    return
            payload = {
                "status": "ok",
                "used_plumber_rows": used_plumber_rows,
                "rows": rows,
                "table_snippets": table_snippets,
                "page_words": page_words if page_words else [],
                "drawing_text": drawing_text,
                "page_texts": page_texts_clean,
                "source": source,
            }
        except Exception as exc:
            payload = {"status": "error", "message": str(exc), "traceback": traceback.format_exc()}
        self.after(0, lambda: self._on_pdf_processed(job_id, payload))

    def _on_pdf_processed(self, job_id, payload):
        if job_id != self._analysis_job:
            return
        self._analysis_in_progress = False
        self.hide_loading()

        status = payload.get("status")
        if status == "error":
            message = payload.get("message") or "Failed to analyze the PDF."
            messagebox.showerror("Processing failed", message)
            self.summary_var.set("Failed to analyze the PDF.")
            self.source_var.set("")
            self.current_file_display = ""
            self.spell_issues = {"rows": {}, "pages": {}}
            self._update_spell_button()
            self.clear_tables()
            self.current_file_var.set("No file loaded")
            self._update_upload_button_state()
            return
        if status == "no_rows":
            messagebox.showwarning("No table rows detected", payload.get("message") or "No table data detected.")
            self.summary_var.set("No table data detected.")
            self.source_var.set("")
            self.current_file_display = ""
            self.spell_issues = {"rows": {}, "pages": {}}
            self._update_spell_button()
            self.clear_tables()
            self.current_file_var.set("No file loaded")
            self._update_upload_button_state()
            return
        if status != "ok":
            self.summary_var.set("Failed to analyze the PDF.")
            self.source_var.set("")
            self.current_file_display = ""
            self.spell_issues = {"rows": {}, "pages": {}}
            self._update_spell_button()
            self.clear_tables()
            self.current_file_var.set("No file loaded")
            self._update_upload_button_state()
            return

        rows = payload["rows"]
        table_snippets = payload["table_snippets"]
        self.drawing_text = payload["drawing_text"]
        self.page_texts = payload["page_texts"]
        self.page_words = payload["page_words"]
        self.table_anchors_by_page = {}
        for row in rows:
            anchor = row.get("table_anchor")
            page_idx = row.get("table_page")
            if anchor and page_idx:
                anchors = self.table_anchors_by_page.setdefault(page_idx, [])
                anchors.append(anchor)
        self._remove_table_words_from_pages(table_snippets)

        pos_analysis = self._analyze_pos_sequence(rows)
        self.pos_analysis = pos_analysis
        duplicate_indices = pos_analysis.get("duplicate_indices", set())
        for idx, row in enumerate(rows):
            row["_pos_duplicate"] = idx in duplicate_indices

        self._spellcache = {}
        results = self.compare_rows(rows, self.drawing_text)
        self.populate_results(results)
        self._latest_results = results  # keep latest results for overlay writer
        self.spell_issues = {"rows": {}, "pages": {}}

        total = len(results)
        pass_count = sum(1 for r in results if r["status"] == "PASS")
        fail_count = total - pass_count
        missing_callout = sum(1 for r in results if not r["callout_found"])
        missing_length = sum(1 for r in results if r["callout_found"] and not r["length_found"])
        missing_thickness = sum(
            1 for r in results if r.get("thickness_required") and r["callout_found"] and not r["thickness_found"]
        )
        thickness_mismatch = sum(
            1 for r in results if r.get("thickness_required") and r["thickness_found"] and not r["thickness_match"]
        )
        summary = (
            f"Overall PASS - {pass_count}/{total} positions matched."
            if fail_count == 0
            else f"Overall FAIL - {fail_count} of {total} positions did not match."
        )
        parts = [summary]
        if missing_callout:
            parts.append(f"Callout missing: {missing_callout}")
        if missing_length:
            parts.append(f"Length missing: {missing_length}")
        if missing_thickness:
            parts.append(f"Thickness missing: {missing_thickness}")
        if thickness_mismatch:
            parts.append(f"Thickness mismatch: {thickness_mismatch}")
        dup_details = pos_analysis.get("duplicate_details") or []
        if dup_details:
            dup_strings = [f"{label}: {pos}" for label, pos in dup_details[:10]]
            more = "..." if len(dup_details) > 10 else ""
            parts.append(f"Duplicate POS: {', '.join(dup_strings)}{more}")
        self._summary_base_parts = parts[:]
        base_summary_text = " | ".join(self._summary_base_parts)
        self.summary_var.set(base_summary_text)
        self._latest_summary_text = base_summary_text
        if fail_count:
            lines = [base_summary_text, ""]
            for r in results:
                if r["status"] == "FAIL":
                    page_note = f" (page {r['drawing_page']})" if r.get("drawing_page") else ""
                    reasons = r.get("failure_reasons") or []
                    detail_reason = "; ".join(reasons) if reasons else "Mismatch"
                    detail = f"{r['pos']} {r['description']}{page_note}: {detail_reason}"
                    lines.append(detail)
                    if len(lines) >= 7:
                        lines.append("...")
                        break
            messagebox.showwarning("Mismatches found", "\n".join(lines))
        else:
            messagebox.showinfo("All matched", base_summary_text)

        self._add_history_entry(self.current_file_display, base_summary_text, results, pos_analysis)
        self._start_spellcheck(results, pos_analysis, self._analysis_job)
        self.current_file_var.set(f"Current file: {self.current_file_display}")
    def _start_loading_animation(self):
        self._stop_loading_animation()
        self.loading_animation_phase = 0
        self.loading_animation_job = self.after(120, self._update_loading_animation)

    def _stop_loading_animation(self):
        if self.loading_animation_job is not None:
            self.after_cancel(self.loading_animation_job)
            self.loading_animation_job = None

    def _update_loading_animation(self):
        phases = ['Thinking.', 'Thinking..', 'Thinking...']
        self.loading_message_var.set(phases[self.loading_animation_phase % len(phases)])
        self.loading_animation_phase += 1
        self.loading_animation_job = self.after(120, self._update_loading_animation)

    def get_pdf_text(self, path):
        text = extract_text_from_pdf(path)
        if text and text.strip():
            return text, "direct extraction"

        if pdfplumber is not None:
            plumber_text = ""
            try:
                with pdfplumber.open(path) as pdf:
                    texts = []
                    for page in pdf.pages:
                        page_text = page.extract_text() or ""
                        if page_text:
                            texts.append(page_text)
                    plumber_text = "\n".join(texts)
            except Exception:
                plumber_text = ""
            if plumber_text.strip():
                return plumber_text, "pdfplumber text"

        if convert_from_path is None or pytesseract is None:
            return "", None

        poppler = self.poppler_path
        if os.name == "nt" and poppler is None:
            if messagebox.askyesno(
                "Poppler required",
                "OCR needs the Poppler bin folder. Do you want to select it now?",
            ):
                selected = filedialog.askdirectory(title="Select poppler/bin folder")
                if not selected:
                    return "", None
                poppler = selected
                self.poppler_path = selected
            else:
                return "", None
        ocr_text = ocr_pdf_to_text(path, poppler_path=poppler)
        return (ocr_text, "OCR") if ocr_text and ocr_text.strip() else ("", None)

    def extract_table_rows(self, text):
        rows = []
        drawing_lines = []
        for line in text.splitlines():
            row = self.parse_table_row(line)
            if row:
                rows.append(row)
            else:
                drawing_lines.append(line)
        if rows:
            for row in rows:
                row.setdefault("table_id", 1)
                row.setdefault("table_label", "Table 1")
        drawing_text = "\n".join(drawing_lines)
        return rows, drawing_text

    @staticmethod
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

    @staticmethod
    def normalize_word_token(text):
        return re.sub(r"[^a-z0-9.+-]", "", text.lower())

    def build_callout_tokens(self, pos, desc):
        tokens = []
        for part in re.split(r"\s+", f"{pos} {desc}"):
            norm = self.normalize_word_token(part)
            if norm:
                tokens.append(norm)
        return tokens

    def _quantity_token_variants(self, quantity_text=None, quantity_value=None):
        variants = []
        seen = set()

        def add_variant(tokens):
            filtered = [tok for tok in tokens if tok]
            if not filtered:
                return
            key = tuple(filtered)
            if key not in seen:
                variants.append(filtered)
                seen.add(key)

        if quantity_text:
            cleaned = quantity_text.strip()
            if cleaned:
                split_tokens = []
                for part in re.split(r"[()\s]+", cleaned):
                    norm = self.normalize_word_token(part)
                    if norm:
                        split_tokens.append(norm)
                add_variant(split_tokens)
                compressed = re.sub(r"[()\s]+", "", cleaned)
                compressed_norm = self.normalize_word_token(compressed)
                if compressed_norm:
                    add_variant([compressed_norm])

        numeric_token = None
        if quantity_value is not None:
            numeric_token = self.normalize_word_token(f"{quantity_value:g}")
            if numeric_token:
                add_variant([numeric_token])

        alpha_in_text = bool(quantity_text and re.search(r"[A-Za-z]", quantity_text))
        if numeric_token and not alpha_in_text:
            for suffix in ("pc", "pcs", "ea", "each", "no", "nos", "off", "qty"):
                add_variant([numeric_token, suffix])
                add_variant([f"{numeric_token}{suffix}"])

        return variants

    def build_callout_token_variants(self, pos, desc, quantity_text=None, quantity_value=None):
        pos_token = ""
        if pos is not None:
            pos_token = self.normalize_word_token(str(pos))

        desc_tokens = []
        for part in re.split(r"\s+", desc or ""):
            norm = self.normalize_word_token(part)
            if norm:
                desc_tokens.append(norm)

        desc_without_pos = [tok for tok in desc_tokens if not pos_token or tok != pos_token]
        primary_tokens = []
        if pos_token:
            primary_tokens.append(pos_token)
        primary_tokens.extend(desc_without_pos if desc_without_pos else desc_tokens)
        if not primary_tokens:
            primary_tokens = ([] if not desc_tokens else list(desc_tokens)) or ([pos_token] if pos_token else [])

        base_tokens = list(primary_tokens)
        variants = []
        seen = set()

        def add_option(tokens):
            filtered = [tok for tok in tokens if tok]
            if not filtered:
                return
            key = tuple(filtered)
            if key not in seen:
                variants.append(filtered)
                seen.add(key)

        quantity_variants = self._quantity_token_variants(quantity_text, quantity_value)
        for qty_tokens in quantity_variants:
            add_option(base_tokens + qty_tokens)

        if pos_token:
            add_option([pos_token])

        add_option(list(base_tokens))

        # fallback variants to tolerate different ordering / redundant tokens in callouts
        if pos_token:
            add_option([pos_token] + desc_tokens)
            add_option(desc_tokens + [pos_token])
        if desc_tokens:
            add_option(list(desc_tokens))
        if desc_without_pos:
            add_option(list(desc_without_pos))

        # generate contiguous subsequences of the description to cope with truncated callouts
        n = len(desc_tokens)
        for i in range(n):
            for j in range(i + 1, n + 1):
                subseq = desc_tokens[i:j]
                if not subseq:
                    continue
                add_option(list(subseq))
                if pos_token:
                    add_option([pos_token] + list(subseq))
                    add_option(list(subseq) + [pos_token])

        return variants, base_tokens

    def show_loading(self, message="Working..."):
        self.loading_message_var.set(message)
        self.loading_overlay.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.loading_overlay.lift()
        self._start_loading_animation()
        self.update_idletasks()

    def hide_loading(self):
        self._stop_loading_animation()
        self.loading_overlay.place_forget()
        self.update_idletasks()

    def _update_upload_button_state(self):
        if not hasattr(self, "upload_button"):
            return
        spellcheck_active = (
            self._spellcheck_thread is not None and self._active_spellcheck_job == self._analysis_job
        )
        busy = self._analysis_in_progress or spellcheck_active
        if busy:
            self.upload_button.state(["disabled"])
        else:
            self.upload_button.state(["!disabled"])


    def clear_tables(self):
        for tab_id in self.table_notebook.tabs():
            widget = self.table_notebook.nametowidget(tab_id)
            self.table_notebook.forget(tab_id)
            widget.destroy()
        self.trees = {}
        self._row_tree_items = {}
        self.spell_tab = None
        self.spell_tree = None

    def _create_table_tree(self, label):
        container = ttk.Frame(self.table_notebook, style="App.TFrame")
        tree = ttk.Treeview(container, columns=self.table_columns, show="headings", height=18, style="Modern.Treeview")
        vsb = ttk.Scrollbar(container, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)

        for col in self.table_columns:
            tree.heading(col, text=self.table_headings[col])
            tree.column(col, width=self.table_column_widths[col], anchor="center")

        tree.tag_configure("pass", background=self.palette["success_bg"], foreground=self.palette["success_fg"])
        tree.tag_configure("fail", background=self.palette["error_bg"], foreground=self.palette["error_fg"])
        tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")

        self.table_notebook.add(container, text=label)
        self.trees[label] = tree
        return tree

    def _tokenize_page_text(self, text):
        tokens = []
        for part in re.split(r"[()\s]+", text):
            norm = self.normalize_word_token(part)
            if norm:
                tokens.append(norm)
        return tokens

    @staticmethod
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

    def _analyze_pos_sequence(self, rows):
        duplicates = set()
        duplicate_indices = set()
        duplicate_details = set()

        # group rows by table id (fallback to page to keep groups separate)
        groups = {}
        for idx, row in enumerate(rows):
            table_key = row.get("table_id")
            if table_key is None:
                table_key = ("page", row.get("table_page"))
            groups.setdefault(table_key, []).append((idx, row))

        for key, entries in groups.items():
            entries.sort(key=lambda item: item[0])
            group_seen = {}
            table_label = entries[0][1].get("table_label")
            if not table_label:
                if isinstance(key, tuple):
                    table_label = f"Page {key[1] or '?'} table"
                else:
                    table_label = f"Table {key}"
            for idx, row in entries:
                pos_raw = row.get("pos")
                pos = (pos_raw or "").strip()
                if not pos:
                    continue

                if pos in group_seen:
                    duplicates.add(pos)
                    duplicate_indices.add(idx)
                    duplicate_indices.add(group_seen[pos])
                    duplicate_details.add((table_label, pos))
                    row["_pos_duplicate"] = True
                else:
                    group_seen[pos] = idx

        return {
            "duplicates": duplicates,
            "duplicate_indices": duplicate_indices,
            "duplicate_details": sorted(duplicate_details),
        }

    @staticmethod
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

    def _candidate_pages_for_tokens(self, token_variants):
        sequences = self._normalize_token_variants(token_variants)
        if not sequences:
            return []
        candidates = []
        for page_idx, text in enumerate(self.page_texts, start=1):
            page_tokens = self._tokenize_page_text(text)
            for tokens in sequences:
                if self.contains_subsequence(page_tokens, tokens):
                    candidates.append(page_idx)
                    break
        return candidates

    def _bbox_in_table_area(self, page_idx, bbox, margin=3.0):
        if not bbox:
            return False
        anchors = self.table_anchors_by_page.get(page_idx) if hasattr(self, "table_anchors_by_page") else None
        if not anchors:
            return False
        x0 = float(bbox.get("x0", 0.0))
        x1 = float(bbox.get("x1", 0.0))
        top = float(bbox.get("top", 0.0))
        bottom = float(bbox.get("bottom", 0.0))
        for anchor in anchors:
            try:
                ax0 = float(anchor.get("x0", 0.0)) - margin
                ax1 = float(anchor.get("x1", 0.0)) + margin
                atop = float(anchor.get("top", 0.0)) - margin
                abottom = float(anchor.get("bottom", 0.0)) + margin
            except Exception:
                continue
            if x1 < ax0 or x0 > ax1 or bottom < atop or top > abottom:
                continue
            return True
        return False

    def _remove_table_words_from_pages(self, table_snippets):
        if not self.page_words or not table_snippets:
            return
        pattern_map = {}
        for page_idx, snippet in table_snippets:
            pieces = []
            for part in re.split(r"\s+", snippet):
                norm = self.normalize_word_token(part)
                if norm:
                    pieces.append(norm)
            if pieces:
                pattern_map.setdefault(page_idx, []).append(pieces)
        for page_idx, patterns in pattern_map.items():
            if page_idx - 1 >= len(self.page_words):
                continue
            words = self.page_words[page_idx - 1]
            norms = [self.normalize_word_token(w.get("text", "")) for w in words]
            remove = set()
            for pattern in patterns:
                plen = len(pattern)
                if plen == 0:
                    continue
                for i in range(len(norms) - plen + 1):
                    if any(not norms[i + j] for j in range(plen)):
                        continue
                    if all(norms[i + j] == pattern[j] for j in range(plen)):
                        match_words = [words[i + j] for j in range(plen)]
                        bbox = {
                            "x0": min((w.get("x0") for w in match_words if w.get("x0") is not None), default=None),
                            "x1": max((w.get("x1") for w in match_words if w.get("x1") is not None), default=None),
                            "top": min((w.get("top") for w in match_words if w.get("top") is not None), default=None),
                            "bottom": max((w.get("bottom") for w in match_words if w.get("bottom") is not None), default=None),
                        }
                        if None in bbox.values():
                            continue
                        if not self._bbox_in_table_area(page_idx, bbox):
                            continue
                        for j in range(plen):
                            remove.add(i + j)
            if remove:
                self.page_words[page_idx - 1] = [
                    word for idx, word in enumerate(words) if idx not in remove
                ]

    @staticmethod
    def _match_callout_on_page(tokens, words):
        if not tokens or not words:
            return None
        normalized_words = []
        for word in words:
            norm = PDFQCApp.normalize_word_token(word.get("text", ""))
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

    @staticmethod
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

    def _find_length_above_bbox(self, words, bbox, desc_numbers, callout_tokens):
        """
        Scan UP from the callout bbox until the nearest barrier:
          - another arrow/callout-like line (e.g., "3.2 TANK"), or
          - a parenthetical tag like "(<pos> NAME...)", or
          - top of page.
        Within that window, collect numeric values near the callout horizontally,
        excluding numbers from the description. Returns (values sorted DESC, bbox map).
        """
        if not words or not bbox:
            return [], {}

        x_margin = max(20.0, (bbox["x1"] - bbox["x0"]) * 0.6)
        bx0 = bbox["x0"] - x_margin
        bx1 = bbox["x1"] + x_margin

        callout_center = (bbox["x0"] + bbox["x1"]) / 2.0
        bbox_top = bbox["top"]

        line_tol = 2.0
        line_groups = {}
        for w in words:
            top = w.get("top")
            bottom = w.get("bottom")
            if top is None or bottom is None:
                continue
            if bottom >= bbox_top - 1.0:
                continue
            key = round(top / line_tol)
            g = line_groups.setdefault(key, {"words": [], "top": top, "bottom": bottom})
            g["words"].append(w)
            g["top"] = min(g["top"], top)
            g["bottom"] = max(g["bottom"], bottom)

        if not line_groups:
            return [], {}

        arrow_like_re = re.compile(r"\b\d+\.\d+\b\s+[A-Za-z]")
        pos_token = callout_tokens[0] if callout_tokens else None
        tag_re = None
        if pos_token:
            tag_re = re.compile(r"\(\s*" + re.escape(pos_token) + r"(?:\s+[A-Za-z0-9._-]+)+\s*\)")

        lines_sorted = sorted(line_groups.values(), key=lambda g: g["bottom"], reverse=True)

        barrier_bottom = None
        collected_words = []
        for g in lines_sorted:
            line_words = sorted(g["words"], key=lambda it: it.get("x0", 0))
            line_text = " ".join((w.get("text", "") or "") for w in line_words)

            is_arrow_like = bool(arrow_like_re.search(line_text))
            is_tag_line = bool(tag_re.search(line_text)) if tag_re else False

            if is_arrow_like or is_tag_line:
                barrier_bottom = g["bottom"]
                break

            for w in line_words:
                x0 = w.get("x0", 0.0)
                x1 = w.get("x1", 0.0)
                center = (x0 + x1) / 2.0
                if bx0 <= center <= bx1:
                    collected_words.append(w)

        if barrier_bottom is not None:
            collected_words = [w for w in collected_words if w.get("bottom", 0) >= barrier_bottom - 0.5]

        candidate_entries = []
        seen_vals = set()

        for w in collected_words:
            values = self._numeric_from_text(w.get("text", ""))
            if not values:
                continue
            x0 = w.get("x0", 0.0)
            x1 = w.get("x1", 0.0)
            center = (x0 + x1) / 2.0
            bbox_info = {
                "x0": float(x0),
                "x1": float(x1),
                "top": float(w.get("top", 0.0)),
                "bottom": float(w.get("bottom", 0.0)),
            }
            for v in values:
                if any(abs(v - dn) <= 1e-6 for dn in desc_numbers):
                    continue
                if v in seen_vals:
                    continue
                seen_vals.add(v)
                candidate_entries.append({
                    "value": v,
                    "center_offset": abs(center - callout_center),
                    "bbox": bbox_info,
                })

        if not candidate_entries:
            return [], {}

        candidate_entries.sort(key=lambda c: (-c["value"], c["center_offset"]))

        ordered_values = []
        value_bboxes = {}
        for entry in candidate_entries:
            v = entry["value"]
            bbox_info = entry["bbox"]
            if v not in value_bboxes:
                value_bboxes[v] = bbox_info
            if not ordered_values or abs(v - ordered_values[-1]) > 1e-6:
                ordered_values.append(v)
        return ordered_values, value_bboxes

    @staticmethod
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

    def _extract_quantity_from_tokens(self, matched_tokens, base_tokens):
        """
        Try to detect a quantity component that follows the POS/description tokens.
        Returns (numeric_value, display_label) or (None, None) if nothing parsable is present.
        """
        if not matched_tokens:
            return None, None

        base_tokens = [tok for tok in (base_tokens or []) if tok]
        tokens = [tok for tok in matched_tokens if tok]

        prefix_len = 0
        for token in base_tokens:
            if prefix_len < len(tokens) and tokens[prefix_len] == token:
                prefix_len += 1
            else:
                break
        quantity_tokens = tokens[prefix_len:]
        if not quantity_tokens:
            return None, None

        suffix_units = {
            "pc": "PC",
            "pcs": "PCS",
            "no": "NO",
            "nos": "NOS",
            "ea": "EA",
            "each": "EACH",
            "set": "SET",
            "sets": "SETS",
            "unit": "UNIT",
            "units": "UNITS",
            "off": "OFF",
            "qty": "QTY",
        }
        prefix_indicators = {"qty", "quantity", "q", "qt"}
        multiplier_indicators = {"x"}

        candidates = []
        seen = set()

        def to_number(text):
            try:
                return float(text)
            except (TypeError, ValueError):
                return None

        def add_candidate(value, unit, weight):
            if value is None:
                return
            if isinstance(value, float):
                if abs(value - round(value)) < 1e-6:
                    value = int(round(value))
            elif not isinstance(value, int):
                return
            label_value = f"{value}" if isinstance(value, int) else f"{value:g}"
            label = label_value if not unit else f"{label_value} {unit}"
            key = (value, unit)
            if key in seen:
                return
            seen.add(key)
            candidates.append((weight, value, label))

        # Inspect individual tokens for embedded quantity patterns.
        for idx, tok in enumerate(quantity_tokens):
            if not tok:
                continue

            # Complete combination: optional prefix + number + optional suffix.
            combo = re.fullmatch(r"([a-z]+)?(\d+(?:\.\d+)?)([a-z]+)?", tok)
            if combo:
                prefix = combo.group(1) or ""
                number = combo.group(2)
                suffix = combo.group(3) or ""
                weight_base = 0
                value = to_number(number)
                unit = None

                if suffix and suffix in suffix_units:
                    unit = suffix_units[suffix]
                    weight_base += 4
                elif suffix and suffix in multiplier_indicators:
                    unit = "PCS"
                    weight_base += 3

                if prefix and prefix in suffix_units and not unit:
                    unit = suffix_units[prefix]
                    weight_base += 3
                elif prefix and prefix in prefix_indicators:
                    weight_base += 2
                elif prefix and prefix in multiplier_indicators and not unit:
                    unit = "PCS"
                    weight_base += 3

                if unit or weight_base:
                    add_candidate(value, unit, max(1, weight_base))
                    continue

            # Number immediately followed by unit token in the next slot.
            if re.fullmatch(r"\d+(?:\.\d+)?", tok):
                value = to_number(tok)
                unit = None
                weight = 1

                if idx + 1 < len(quantity_tokens):
                    nxt = quantity_tokens[idx + 1]
                    if nxt in suffix_units:
                        unit = suffix_units[nxt]
                        weight = 4
                    elif nxt in multiplier_indicators:
                        unit = "PCS"
                        weight = 3

                if unit is None and idx > 0:
                    prev = quantity_tokens[idx - 1]
                    if prev in suffix_units:
                        unit = suffix_units[prev]
                        weight = 3
                    elif prev in prefix_indicators:
                        weight = max(weight, 2)

                if unit is None and len(quantity_tokens) == 1:
                    weight = max(weight, 2)

                add_candidate(value, unit, weight)
                continue

            # Unit token followed or preceded by number elsewhere (e.g., "pcs", "qty").
            if tok in suffix_units or tok in prefix_indicators or tok in multiplier_indicators:
                for direction in (1, -1):
                    j = idx + direction
                    if 0 <= j < len(quantity_tokens):
                        neighbour = quantity_tokens[j]
                        if re.fullmatch(r"\d+(?:\.\d+)?", neighbour):
                            value = to_number(neighbour)
                            if tok in suffix_units:
                                unit = suffix_units[tok]
                                weight = 4
                            elif tok in multiplier_indicators:
                                unit = "PCS"
                                weight = 3
                            else:
                                unit = None
                                weight = 2
                            add_candidate(value, unit, weight)
                            break

            # Multiplication style token such as "2x" or "x2".
            if re.fullmatch(r"\d+(?:\.\d+)?x", tok):
                value = to_number(tok[:-1])
                add_candidate(value, "PCS", 3)
                continue
            if re.fullmatch(r"x\d+(?:\.\d+)?", tok):
                value = to_number(tok[1:])
                add_candidate(value, "PCS", 3)
                continue

        if not candidates:
            return None, None

        candidates.sort(key=lambda item: item[0], reverse=True)
        _, value, label = candidates[0]
        return value, label

    def _geometry_lookup(self, token_variants, desc_numbers, expected_value, prefer_max, base_length, base_tokens):
        if not self.page_words:
            return False, None, None, {"quantity_tokens": False, "quantity_value": None}
        sequences = self._normalize_token_variants(token_variants)
        if not sequences:
            return False, None, None, {"quantity_tokens": False, "quantity_value": None}
        candidate_pages = self._candidate_pages_for_tokens(sequences)
        if not candidate_pages:
            candidate_pages = list(range(1, len(self.page_words) + 1))
        fallback_page = None
        for page_idx in candidate_pages:
            if page_idx - 1 >= len(self.page_words):
                continue
            words = self.page_words[page_idx - 1]
            matched_tokens = None
            bbox = None
            for tokens in sequences:
                bbox = self._match_callout_on_page(tokens, words)
                if bbox and self._bbox_in_table_area(page_idx, bbox):
                    bbox = None
                    continue
                if bbox:
                    matched_tokens = tokens
                    break
            if not bbox:
                continue
            fallback_page = page_idx
            candidates, candidate_bboxes = self._find_length_above_bbox(words, bbox, desc_numbers, matched_tokens)
            best_value, selection_mode = self._pick_candidate(candidates, expected_value, prefer_max)
            value_bbox = candidate_bboxes.get(best_value) if best_value is not None else None
            quantity_value, quantity_label = self._extract_quantity_from_tokens(matched_tokens or [], base_tokens)
            quantity_tokens = bool(
                quantity_value is not None
                or (matched_tokens and base_length is not None and len(matched_tokens) > max(base_length, 0))
            )
            meta = {
                "method": "geometry",
                "candidates": candidates,
                "selection": selection_mode,
                "bbox": bbox,
                "value_bbox": value_bbox,
                "candidate_bboxes": candidate_bboxes,
                "tokens": matched_tokens,
                "quantity_tokens": quantity_tokens,
                "quantity_value": quantity_value,
                "quantity_label": quantity_label,
            }
            if best_value is not None:
                return True, best_value, page_idx, meta
            return True, None, page_idx, meta
        if fallback_page is not None:
            selection_mode = "max_in_window" if prefer_max or expected_value is None else "closest_to_expected"
            return True, None, fallback_page, {
                "method": "geometry",
                "candidates": [],
                "selection": selection_mode,
                "bbox": None,
                "value_bbox": None,
                "candidate_bboxes": {},
                "tokens": None,
                "quantity_tokens": False,
                "quantity_value": None,
                "quantity_label": None,
            }
        return False, None, None, {"quantity_tokens": False, "quantity_value": None, "quantity_label": None}

    def _text_lookup(self, token_variants, desc_numbers, expected_value, prefer_max, base_length, base_tokens):
        if not self.page_texts:
            return False, None, None, {"quantity_tokens": False}
        sequences = self._normalize_token_variants(token_variants)
        if not sequences:
            return False, None, None, {"quantity_tokens": False}
        for page_idx, text in enumerate(self.page_texts, start=1):
            lines = text.splitlines()
            for idx, line in enumerate(lines):
                line_tokens = self._tokenize_page_text(line)
                matched_tokens = None
                for tokens in sequences:
                    if self.contains_subsequence(line_tokens, tokens):
                        matched_tokens = tokens
                        break
                if matched_tokens:
                    quantity_value, quantity_label = self._extract_quantity_from_tokens(matched_tokens or [], base_tokens)
                    quantity_tokens = bool(
                        quantity_value is not None
                        or (matched_tokens and base_length is not None and len(matched_tokens) > max(base_length, 0))
                    )
                    candidate_lines = [line]
                    if idx + 1 < len(lines):
                        candidate_lines.append(lines[idx + 1])
                    for cand in candidate_lines:
                        match = re.search(r"(\d+(?:[,\s]\d{3})*(?:\.\d+)?)\s*mm", cand, flags=re.IGNORECASE)
                        if match:
                            try:
                                value = float(match.group(1).replace(",", "").replace(" ", ""))
                                candidates = [value]
                                best_value, selection_mode = self._pick_candidate(
                                    candidates, expected_value, prefer_max
                                )
                                return True, best_value, page_idx, {
                                    "method": "text",
                                    "candidates": candidates,
                                    "selection": selection_mode,
                                    "tokens": matched_tokens,
                                    "quantity_tokens": quantity_tokens,
                                    "quantity_value": quantity_value,
                                    "quantity_label": quantity_label,
                                }
                            except ValueError:
                                continue
                    numbers = []
                    for cand in candidate_lines:
                        numbers.extend(self.extract_numeric_values(cand))
                    if expected_value is not None:
                        min_threshold = min(20.0, max(1.0, expected_value * 0.5))
                    else:
                        min_threshold = 20.0
                    numbers = [
                        n for n in numbers
                        if n >= min_threshold and all(abs(n - dn) > 1e-6 for dn in desc_numbers)
                    ]
                    if numbers:
                        numbers.sort(reverse=True)
                        best_value, selection_mode = self._pick_candidate(numbers, expected_value, prefer_max)
                        return True, best_value, page_idx, {
                            "method": "text",
                            "candidates": numbers,
                            "selection": selection_mode,
                            "tokens": matched_tokens,
                            "quantity_tokens": quantity_tokens,
                            "quantity_value": quantity_value,
                            "quantity_label": quantity_label,
                        }
                    return True, None, page_idx, {
                        "method": "text",
                        "candidates": [],
                        "selection": "none",
                        "tokens": matched_tokens,
                        "quantity_tokens": quantity_tokens,
                        "quantity_value": quantity_value,
                        "quantity_label": quantity_label,
                    }
        return False, None, None, {"quantity_tokens": False, "quantity_value": None, "quantity_label": None}

    def _find_value_for_row(self, pos, desc, expected_value, prefer_max, quantity_text=None, quantity_value=None):
        token_variants, base_tokens = self.build_callout_token_variants(pos, desc, quantity_text, quantity_value)
        base_length = len(base_tokens)
        desc_numbers = set(self.extract_numeric_values(desc))
        callout_found, value, page_idx, meta = self._geometry_lookup(
            token_variants, desc_numbers, expected_value, prefer_max, base_length, base_tokens
        )
        if callout_found:
            return callout_found, value, page_idx, meta
        return self._text_lookup(token_variants, desc_numbers, expected_value, prefer_max, base_length, base_tokens)

    def find_length_for_row(self, pos, desc, expected_length=None, quantity_text=None, quantity_value=None):
        return self._find_value_for_row(
            pos, desc, expected_length, prefer_max=True, quantity_text=quantity_text, quantity_value=quantity_value
        )

    def find_thickness_for_row(self, pos, desc, expected_thickness, quantity_text=None, quantity_value=None):
        if expected_thickness is None:
            return False, None, None, {}
        return self._find_value_for_row(
            pos, desc, expected_thickness, prefer_max=False, quantity_text=quantity_text, quantity_value=quantity_value
        )

    @staticmethod
    def tokenize(text):
        return [tok for tok in re.split(r"[^a-z0-9]+", text.lower()) if tok]

    @staticmethod
    def contains_subsequence(tokens, subseq):
        if not subseq:
            return False
        n = len(subseq)
        for i in range(len(tokens) - n + 1):
            if tokens[i:i + n] == subseq:
                return True
        return False

    @staticmethod
    def extract_numeric_values(text):
        values = []
        for match in re.finditer(r"\d+(?:[,\s]\d{3})*(?:\.\d+)?", text):
            candidate = match.group(0).replace(" ", "").replace(",", "")
            try:
                values.append(float(candidate))
            except ValueError:
                continue
        return values

    def compare_rows(self, rows, drawing_text):
        results = []
        tolerance = 0.5
        for row_index, row in enumerate(rows):
            expected_lengths = row.get("length_options") or ([row["length"]] if row.get("length") is not None else [])
            length_required = bool(expected_lengths)
            expected_primary = expected_lengths[0] if expected_lengths else None
            quantity_value = row.get("quantity")
            quantity_text = row.get("callout_quantity_text") or row.get("quantity_display")
            if not quantity_text and quantity_value is not None:
                if isinstance(quantity_value, (int, float)):
                    if abs(quantity_value - int(quantity_value)) < 1e-6:
                        quantity_text = str(int(quantity_value))
                    else:
                        quantity_text = f"{quantity_value:g}"
                else:
                    quantity_text = str(quantity_value)
            length_callout, drawing_length, length_page, length_meta = self.find_length_for_row(
                row["pos"], row["description"], expected_primary, quantity_text, quantity_value
            )
            length_candidates = length_meta.get("candidates", []) if length_meta else []
            length_method = length_meta.get("method") if length_meta else None
            length_selection = length_meta.get("selection") if length_meta else None
            length_quantity_tokens = bool(length_meta.get("quantity_tokens")) if length_meta else False
            length_found = drawing_length is not None
            length_match = not length_required
            if drawing_length is not None and expected_lengths:
                for expected in expected_lengths:
                    if abs(drawing_length - expected) <= tolerance:
                        length_match = True
                        break
                if not length_match:
                    length_match = False
            else:
                if length_required:
                    length_match = False

            thickness_expected = row.get("thickness")
            thickness_required = thickness_expected is not None
            thickness_callout = False
            drawing_thickness = None
            thickness_page = None
            thickness_meta = {}
            thickness_candidates = []
            thickness_method = None
            thickness_selection = None
            thickness_found = False
            thickness_match = not thickness_required
            thickness_quantity_tokens = False
            if thickness_required:
                thickness_callout, drawing_thickness, thickness_page, thickness_meta = self.find_thickness_for_row(
                    row["pos"], row["description"], thickness_expected, quantity_text, quantity_value
                )
                thickness_candidates = thickness_meta.get("candidates", []) if thickness_meta else []
                thickness_method = thickness_meta.get("method") if thickness_meta else None
                thickness_selection = thickness_meta.get("selection") if thickness_meta else None
                thickness_quantity_tokens = bool(thickness_meta.get("quantity_tokens")) if thickness_meta else False
                thickness_found = drawing_thickness is not None
                if drawing_thickness is not None and thickness_expected is not None:
                    if abs(drawing_thickness - thickness_expected) <= tolerance:
                        thickness_match = True
                    else:
                        thickness_match = False
                else:
                    thickness_match = False

            callout_found = length_callout or thickness_callout
            failure_reasons = []
            info_notes = []
            length_quantity_value = length_meta.get("quantity_value") if length_meta else None
            length_quantity_label = length_meta.get("quantity_label") if length_meta else None
            thickness_quantity_value = thickness_meta.get("quantity_value") if thickness_meta else None
            thickness_quantity_label = thickness_meta.get("quantity_label") if thickness_meta else None
            quantity_tokens_flag = length_quantity_tokens or thickness_quantity_tokens

            quantity_values = []
            quantity_labels = []
            if length_quantity_value is not None:
                quantity_values.append(length_quantity_value)
            if thickness_quantity_value is not None:
                quantity_values.append(thickness_quantity_value)
            if length_quantity_label:
                quantity_labels.append(length_quantity_label)
            if thickness_quantity_label:
                quantity_labels.append(thickness_quantity_label)

            quantity_callout_value = None
            if quantity_values:
                quantity_callout_value = quantity_values[0]
                for candidate in quantity_values[1:]:
                    if abs(candidate - quantity_callout_value) > 1e-6:
                        info_notes.append("qty conflict detected in callout")
                        break

            quantity_callout_label = None
            if quantity_labels:
                quantity_callout_label = quantity_labels[0]
            elif quantity_callout_value is not None:
                if isinstance(quantity_callout_value, float) and abs(quantity_callout_value - int(quantity_callout_value)) < 1e-6:
                    quantity_callout_label = str(int(quantity_callout_value))
                else:
                    quantity_callout_label = f"{quantity_callout_value:g}"

            quantity_callout_found = bool(quantity_callout_label or quantity_callout_value is not None)
            if not callout_found:
                quantity_callout_found = False
                quantity_callout_value = None
                quantity_callout_label = None
            table_label = row.get("table_label")
            if not table_label:
                if row.get("table_id") is not None:
                    table_label = f"Table {row['table_id']}"
                elif row.get("table_page"):
                    table_label = f"Page {row['table_page']}"
                else:
                    table_label = "table"
            if row.get("_pos_duplicate"):
                failure_reasons.append(f"duplicate POS in {table_label}")

            if not callout_found:
                failure_reasons.append("callout missing")

            if callout_found:
                if not length_found and length_required:
                    if length_method == "geometry":
                        if length_candidates:
                            failure_reasons.append("length missing (no candidate matched table)")
                        else:
                            failure_reasons.append("length missing (no numeric in window)")
                    elif length_method == "text":
                        failure_reasons.append("length missing (text search)")
                    else:
                        failure_reasons.append("length missing")
                elif length_found and not length_match:
                    expected_note = row.get("length_display")
                    if not expected_note:
                        expected_note = " / ".join(f"{v:.1f}" for v in expected_lengths) if expected_lengths else ""
                    if expected_note:
                        failure_reasons.append(f"length mismatch: drawing {drawing_length:.1f} vs table {expected_note}")

                if length_method == "geometry":
                    if length_candidates:
                        others = [v for v in length_candidates if drawing_length is None or abs(v - drawing_length) > 1e-6]
                        if others:
                            top_vals = ", ".join(f"{v:.1f}" for v in others[:3])
                            info_notes.append(f"other dims in window: {top_vals}")
                    if length_selection == "max_in_window":
                        info_notes.append("picked highest value within barrier window")
                    elif length_selection == "closest_to_expected":
                        info_notes.append("picked value closest to expected")
                elif length_method == "text":
                    info_notes.append("length from text fallback")

                if thickness_required:
                    if callout_found and not thickness_found:
                        failure_reasons.append("thickness missing")
                    elif thickness_found and not thickness_match:
                        expected_thk_note = row.get("thickness_display")
                        if not expected_thk_note and thickness_expected is not None:
                            expected_thk_note = f"{thickness_expected:.1f}"
                        failure_reasons.append(
                            f"thickness mismatch: drawing {drawing_thickness:.1f} vs table {expected_thk_note}"
                        )
                    if thickness_method == "text":
                        info_notes.append("thickness from text fallback")

                if row.get("quantity_display"):
                    if quantity_callout_found:
                        pass
                    elif quantity_tokens_flag:
                        info_notes.append("qty present in callout text but not parsed")
                    else:
                        info_notes.append("qty missing in callout")

            length_ok = length_match
            thickness_ok = (not thickness_required) or (thickness_found and thickness_match)
            pos_ok = not row.get("_pos_duplicate")
            status = "PASS" if callout_found and length_ok and thickness_ok and pos_ok else "FAIL"

            failure_details = list(failure_reasons)
            info_details = list(info_notes)

            results.append({
                **row,
                "_row_index": row_index,
                "length_required": length_required,
                "callout_found": callout_found,
                "length_found": length_found,
                "length_match": length_match,
                "drawing_length": drawing_length,
                "drawing_page": length_page,
                "drawing_method": length_method,
                "selection_rule": length_selection,
                "candidate_lengths": length_candidates,
                "thickness_required": thickness_required,
                "thickness_callout_found": thickness_callout,
                "thickness_found": thickness_found,
                "thickness_match": thickness_match,
                "drawing_thickness": drawing_thickness,
                "thickness_page": thickness_page,
                "thickness_method": thickness_method,
                "thickness_selection_rule": thickness_selection,
                "candidate_thicknesses": thickness_candidates,
                "quantity_callout_found": quantity_callout_found,
                "quantity_callout": quantity_callout_value,
                "quantity_callout_label": quantity_callout_label,
                "quantity_tokens_detected": quantity_tokens_flag,
                "status": status,
                "failure_reasons": failure_details,
                "info_notes": info_details,
                "callout_bbox": length_meta.get("bbox") if length_meta else None,
                "length_bbox": length_meta.get("value_bbox") if length_meta else None,
                "thickness_bbox": thickness_meta.get("value_bbox") if thickness_meta else None,
            })
        return results

    @staticmethod
    def format_length(value):
        text = f"{value:.3f}".rstrip("0").rstrip(".")
        return f"{text} mm"

    def populate_results(self, results):
        self.clear_tables()
        if not results:
            return

        def resolve_label(row):
            label = row.get("table_label")
            if label:
                return label
            if row.get("table_id") is not None:
                return f"Table {row['table_id']}"
            if row.get("table_page"):
                return f"Page {row['table_page']}"
            return "All results"

        def format_quantity_value(value):
            if value is None:
                return ""
            if isinstance(value, (int, float)):
                if isinstance(value, float) and abs(value - int(value)) < 1e-6:
                    return str(int(value))
                return f"{value:.2f}".rstrip("0").rstrip(".")
            return str(value)

        table_groups = {}
        table_order = []
        for row in results:
            label = resolve_label(row)
            if label not in table_groups:
                table_groups[label] = []
                table_order.append(label)
            table_groups[label].append(row)

        pending_check = self._spellcheck_thread is not None and self._active_spellcheck_job == self._analysis_job
        completed_job = (not pending_check) and (self._spell_last_completed_job == self._analysis_job)
        self._row_tree_items = {}

        for label in table_order:
            tree = self._create_table_tree(label)
            for row in table_groups[label]:
                drawing_length_display = ""
                if row.get("length_found") and row.get("drawing_length") is not None:
                    drawing_length_display = self.format_length(row["drawing_length"])
                    page_note = row.get("drawing_page")
                    if page_note:
                        page_str = str(page_note)
                        digits_only = "".join(ch for ch in page_str if ch.isdigit())
                        page_label = digits_only if digits_only else page_str
                        drawing_length_display += f" (Sheet {page_label})"
                quantity_display = row.get("quantity_display")
                if not quantity_display:
                    qty_value = row.get("quantity")
                    if qty_value is not None:
                        quantity_display = format_quantity_value(qty_value)
                    else:
                        quantity_display = ""
                qty_display_text = quantity_display or "-"

                callout_label = row.get("quantity_callout_label")
                callout_value = row.get("quantity_callout")
                callout_found_flag = bool(row.get("callout_found"))
                quantity_callout_found = bool(row.get("quantity_callout_found"))
                callout_text = ""
                if callout_found_flag and quantity_callout_found:
                    callout_text = callout_label or format_quantity_value(callout_value)
                elif callout_found_flag and row.get("quantity_tokens_detected"):
                    callout_text = "Callout detected (unparsed)"
                elif callout_found_flag:
                    callout_text = "Callout missing"
                else:
                    callout_text = "Callout missing"

                if callout_text:
                    quantity_display = f"{qty_display_text} / {callout_text}"
                else:
                    quantity_display = qty_display_text
                table_length_display = row.get("length_display")
                options = row.get("length_options")
                if not table_length_display:
                    if options and len(options) > 1:
                        table_length_display = " / ".join(self.format_length(v) for v in options)
                    elif options:
                        table_length_display = self.format_length(options[0])
                    else:
                        table_length_display = self.format_length(row["length"])
                table_thickness_display = row.get("thickness_display")
                if not table_thickness_display and row.get("thickness") is not None:
                    table_thickness_display = self.format_length(row["thickness"])
                drawing_thickness_display = ""
                if row.get("thickness_found") and row.get("drawing_thickness") is not None:
                    drawing_thickness_display = self.format_length(row["drawing_thickness"])
                    page_note = row.get("thickness_page")
                    if page_note:
                        page_str = str(page_note)
                        digits_only = "".join(ch for ch in page_str if ch.isdigit())
                        page_label = digits_only if digits_only else page_str
                        drawing_thickness_display += f" (Sheet {page_label})"

                table_length_text = table_length_display or "-"
                if not row.get("callout_found"):
                    length_bom_display = "Callout missing"
                    length_dwg_display = "Callout missing"
                else:
                    length_bom_display = table_length_text if table_length_text and table_length_text != "-" else "-"
                    length_dwg_display = drawing_length_display or "Callout missing"
                table_thickness_text = table_thickness_display or "-"
                if not row.get("thickness_found"):
                    thickness_bom_display = table_thickness_text if table_thickness_text and table_thickness_text != "-" else "-"
                    thickness_dwg_display = "Callout missing"
                else:
                    thickness_bom_display = table_thickness_text if table_thickness_text and table_thickness_text != "-" else "-"
                    thickness_dwg_display = drawing_thickness_display or "Callout missing"

                values = (
                    row["pos"],
                    row["description"],
                    quantity_display,
                    length_bom_display,
                    length_dwg_display,
                    thickness_bom_display,
                    thickness_dwg_display,
                )
                tag = "pass" if row["status"] == "PASS" else "fail"
                tree.insert("", "end", values=values, tags=(tag,))

        # focus first tab for convenience
        if self.table_notebook.tabs():
            self.table_notebook.select(self.table_notebook.tabs()[0])
        self._refresh_spell_column(pending_check)
        self._show_spell_tab_pending()

    def _add_history_entry(self, file_name, summary_text, results, pos_analysis=None):
        if not file_name or not results:
            return
        entry = {
            "file": file_name,
            "summary": summary_text,
            "results": copy.deepcopy(results),
            "pos_analysis": copy.deepcopy(pos_analysis) if pos_analysis else None,
            "spell_issues": copy.deepcopy(self.spell_issues),
        }
        self.history_entries = [e for e in self.history_entries if e["file"] != file_name]
        self.history_entries.insert(0, entry)
        if len(self.history_entries) > 3:
            self.history_entries = self.history_entries[:3]
        self._update_history_ui()

    def _update_history_ui(self):
        if self.history_buttons_frame is None:
            return
        for child in self.history_buttons_frame.winfo_children():
            child.destroy()
        if not self.history_entries:
            ttk.Label(
                self.history_buttons_frame,
                text="No recent files yet.",
                style="CardMuted.TLabel",
                justify="left",
            ).pack(anchor="w")
            return
        for idx, entry in enumerate(self.history_entries):
            display_text = f"{idx + 1}. {entry['file']}"
            stateful_style = "HistorySelected.TButton" if entry["file"] == self.current_file_display else "History.TButton"
            btn = ttk.Button(
                self.history_buttons_frame,
                text=display_text,
                style=stateful_style,
                command=lambda i=idx: self._load_history_entry(i),
            )
            btn.pack(anchor="w", fill="x", pady=2)
            if entry["file"] == self.current_file_display:
                btn.configure(text=f"• {display_text}")

    def _load_history_entry(self, index):
        if index < 0 or index >= len(self.history_entries):
            return
        entry = self.history_entries[index]
        results_copy = copy.deepcopy(entry["results"])
        self.current_file_display = entry["file"]
        self.summary_var.set(entry["summary"])
        self.source_var.set(f"File: {entry['file']} (history)")
        if entry.get("pos_analysis") is not None:
            self.pos_analysis = copy.deepcopy(entry["pos_analysis"])
        else:
            self.pos_analysis = {}
        stored = entry.get("spell_issues") or {"rows": {}, "pages": {}}
        self.spell_issues = copy.deepcopy(stored)
        self._spellcheck_thread = None
        self._active_spellcheck_job = 0
        self._spell_last_completed_job = self._analysis_job
        self.populate_results(results_copy)
        self._latest_results = results_copy
        self._refresh_spell_column(pending=False)
        self._populate_spell_tab(self.spell_issues)
        self.current_file_var.set(f"Current file: {self.current_file_display} (history)")
        self._update_history_ui()

    def _get_spell_checker(self):
        if self.spell_checker is False:
            return None
        if SpellChecker is None:
            self.spell_checker = False
            return None
        if self.spell_checker is None:
            try:
                self.spell_checker = SpellChecker()
            except Exception:
                self.spell_checker = False
        return self.spell_checker if self.spell_checker is not False else None

    def _spellcheck_rows(self, rows):
        checker = self._get_spell_checker()
        if checker is None:
            return {"rows": {}, "pages": {}}

        cache = self._spellcache if isinstance(self._spellcache, dict) else {}

        def analyze_text(text):
            text_original = text or ""
            key = text_original.strip().lower()
            if not key:
                return {}
            if key in cache:
                return cache[key]

            tokens = re.findall(r"[A-Za-z']+", text_original)
            original_words = {}
            filtered = set()
            for raw_token in tokens:
                token = raw_token
                if not token:
                    continue
                lower = token.lower()
                if len(lower) <= 3:
                    continue
                if lower.startswith("http") or lower.startswith("www"):
                    continue
                if len(lower) <= 2:
                    continue
                if any(char.isdigit() for char in token):
                    continue
                if lower in SPELLCHECK_ALLOWLIST:
                    continue
                if lower not in filtered:
                    original_words.setdefault(lower, raw_token)
                    filtered.add(lower)
            if not filtered:
                return {}
            unknown = checker.unknown(filtered)
            results = {}
            for word in unknown:
                if word in SPELLCHECK_ALLOWLIST:
                    continue
                original = original_words.get(word, word)
                if word in results:
                    continue
                suggestions = []
                try:
                    candidates = sorted(checker.candidates(word))
                except Exception:
                    candidates = []
                for cand in candidates:
                    if cand and cand.lower() != word:
                        suggestions.append(cand)
                    if len(suggestions) >= 3:
                        break
                results[word] = (original, suggestions)
            cache[key] = results
            if len(cache) > 2000:
                cache.clear()
            return results

        row_issues = {}
        for idx, row in enumerate(rows):
            contexts = []
            description = row.get("description")
            if description:
                contexts.append(description)
            label = row.get("table_label")
            if label:
                contexts.append(str(label))
            for note in row.get("info_notes") or []:
                if note:
                    contexts.append(str(note))
            row_issue_entries = []
            seen = set()
            for text in contexts:
                issues_map = analyze_text(text)
                for word, (original, suggestions) in issues_map.items():
                    key = (word.lower(), text)
                    if key in seen:
                        continue
                    seen.add(key)
                    row_issue_entries.append((original, suggestions, text))
            if row_issue_entries:
                row_issues[idx] = row_issue_entries

        page_issues = {}
        for page_idx, text in enumerate(self.page_texts or [], start=1):
            entries = []
            seen = set()
            for line in (text or "").splitlines():
                stripped = line.strip()
                if not stripped:
                    continue
                issues_map = analyze_text(stripped)
                for word, (original, suggestions) in issues_map.items():
                    key = (word.lower(), stripped)
                    if key in seen:
                        continue
                    seen.add(key)
                    entries.append((original, suggestions, stripped))
            if entries:
                page_issues[page_idx] = entries

        return {"rows": row_issues, "pages": page_issues}

    def _update_spell_button(self):
        if not hasattr(self, "spell_button") or self.spell_button is None:
            return
        rows = self.spell_issues.get("rows", {}) if isinstance(self.spell_issues, dict) else {}
        total_words = sum(len(v) for v in rows.values())

        if self.spell_checker is False or (SpellChecker is None and total_words == 0):
            self.spell_button.configure(text="Spelling check unavailable")
            self.spell_button.state(["disabled"])
            return

        if total_words:
            label = f"Spelling issues ({total_words} word{'s' if total_words != 1 else ''})"
            self.spell_button.configure(text=label)
            self.spell_button.state(["!disabled"])
        else:
            self.spell_button.configure(text="No spelling issues")
            self.spell_button.state(["disabled"])

    def _spell_status_text(self, row_idx, pending=False, completed=False):
        if row_idx is None:
            return ""
        rows_map = self.spell_issues.get("rows", {}) if isinstance(self.spell_issues, dict) else {}
        issues = rows_map.get(row_idx)
        if issues:
            pieces = []
            for word, suggestions, _ in issues[:2]:
                if suggestions:
                    pieces.append(f"{word}->{suggestions[0]}")
                else:
                    pieces.append(word)
            if len(issues) > 2:
                pieces.append("...")
            return "; ".join(pieces)
        if pending:
            return "Checking..."
        if completed:
            return "OK"
        return ""

    def _refresh_spell_column(self, pending=None):
        if pending is None:
            pending = self._spellcheck_thread is not None and self._active_spellcheck_job == self._analysis_job
        completed = (not pending) and (self._spell_last_completed_job == self._analysis_job)
        row_items = getattr(self, "_row_tree_items", {})
        for row_idx, ref in row_items.items():
            tree, item_id = ref
            try:
                tree.set(item_id, "spell_status", self._spell_status_text(row_idx, pending, completed))
            except tk.TclError:
                continue

    def _ensure_spell_tab(self):
        if self.spell_tab is not None and self.spell_tab in self.table_notebook.tabs() and self.spell_tree is not None:
            return
        container = ttk.Frame(self.table_notebook, style="App.TFrame")
        columns = ("location", "word", "suggestions")
        tree = ttk.Treeview(container, columns=columns, show="headings", height=12, style="Modern.Treeview")
        headings = {
            "location": "Location",
            "word": "Word",
            "suggestions": "Suggestions",
        }
        widths = {
            "location": 200,
            "word": 120,
            "suggestions": 160,
        }
        for col in columns:
            tree.heading(col, text=headings[col])
            tree.column(col, width=widths[col], anchor="center")
        vsb = ttk.Scrollbar(container, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.table_notebook.add(container, text="Spelling Issues")
        self.spell_tab = self.table_notebook.tabs()[-1]
        self.spell_tree = tree

    def _show_spell_tab_pending(self):
        self._ensure_spell_tab()
        tree = self.spell_tree
        if tree is None:
            return
        for item in tree.get_children():
            tree.delete(item)
        item = tree.insert("", "end", values=("", "", "Spelling check running..."))
        tree.tag_bind(item, "<Double-1>", lambda _e: None)

    def _populate_spell_tab(self, issues):
        self._ensure_spell_tab()
        tree = self.spell_tree
        if tree is None:
            return
        for item in tree.get_children():
            tree.delete(item)

        entries = []
        rows_map = issues.get("rows", {}) if isinstance(issues, dict) else {}
        for idx, issue_list in rows_map.items():
            if idx < len(self._latest_results):
                row = self._latest_results[idx]
                label = row.get("table_label") or ""
                pos = row.get("pos") or ""
                description = row.get("description") or ""
                location = " ".join(part for part in [label, f"POS {pos}".strip()] if part).strip()
                if not location:
                    location = f"Row {idx + 1}"
                context_base = description
            else:
                location = f"Row {idx + 1}"
                context_base = ""
            for word, suggestions, context in issue_list:
                suggestion_text = ", ".join(suggestions) if suggestions else ""
                entries.append((location, word, suggestion_text))

        pages_map = issues.get("pages", {}) if isinstance(issues, dict) else {}
        for page_idx, issue_list in pages_map.items():
            location = f"Page {page_idx}"
            for word, suggestions, context in issue_list:
                suggestion_text = ", ".join(suggestions) if suggestions else ""
                entries.append((location, word, suggestion_text))

        if not entries:
            tree.insert("", "end", values=("", "", "No spelling issues"))
            return

        for location, word, suggestion_text in entries:
            item = tree.insert("", "end", values=(location, word, suggestion_text))
            tree.tag_bind(item, "<Double-1>", lambda _e, w=word: self._copy_word_to_clipboard(w))

    def _copy_word_to_clipboard(self, word):
        try:
            self.clipboard_clear()
            self.clipboard_append(word)
        except tk.TclError:
            pass

    def show_spelling_issues(self):
        rows = self.spell_issues.get("rows", {}) if isinstance(self.spell_issues, dict) else {}
        total_words = sum(len(v) for v in rows.values())

        if total_words == 0:
            if self.spell_checker is False or SpellChecker is None:
                messagebox.showinfo(
                    "Spelling check",
                    "Install the 'pyspellchecker' package to enable spelling checks.",
                )
            else:
                messagebox.showinfo("Spelling check", "No spelling issues detected.")
            return

        dialog = tk.Toplevel(self)
        dialog.title("Spelling issues")
        dialog.configure(bg=self.palette["bg"])
        dialog.geometry("520x360")
        dialog.transient(self)
        dialog.grab_set()

        container = ttk.Frame(dialog, padding=16, style="App.TFrame")
        container.pack(fill="both", expand=True)

        header = ttk.Label(
            container,
            text="Words flagged by the spelling checker",
            style="SummaryTitle.TLabel",
        )
        header.pack(anchor="w")

        tree = ttk.Treeview(
            container,
            columns=("location", "word", "suggestions"),
            show="headings",
            height=10,
            style="Modern.Treeview",
        )
        tree.heading("location", text="Location")
        tree.heading("word", text="Word")
        tree.heading("suggestions", text="Suggestions")
        tree.column("location", width=140, anchor="w")
        tree.column("word", width=130, anchor="w")
        tree.column("suggestions", width=220, anchor="w")
        vsb = ttk.Scrollbar(container, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side="left", fill="both", expand=True, pady=(12, 0))
        vsb.pack(side="right", fill="y", pady=(12, 0))

        copy_frame = ttk.Frame(container, padding=(0, 12, 0, 0), style="App.TFrame")
        copy_frame.pack(fill="x", expand=False)

        def copy_selected():
            selected = tree.selection()
            if not selected:
                return
            rows_text = []
            for item in selected:
                values = tree.item(item, "values")
                if values:
                    rows_text.append("\t".join(values))
            if rows_text:
                self.clipboard_clear()
                self.clipboard_append("\n".join(rows_text))

        ttk.Button(
            copy_frame,
            text="Copy selected",
            style="Secondary.TButton",
            command=copy_selected,
        ).pack(anchor="e")

        def render_issue(location, issue_list):
            for word, suggestions in issue_list:
                suggestion_text = ", ".join(suggestions) if suggestions else "no suggestion"
                tree.insert("", "end", values=(location, word, suggestion_text))

        for idx, issue_list in rows.items():
            if idx < len(self._latest_results):
                row = self._latest_results[idx]
                row_text = " ".join(part for part in [(row.get("pos") or "").strip(), row.get("description") or ""] if part)
                if row_text:
                    location = f"Row {idx + 1} ({row_text})"
                else:
                    location = f"Row {idx + 1}"
            else:
                location = f"Row {idx + 1}"
            render_issue(location, issue_list)

        ttk.Button(
            container,
            text="Close",
            style="Secondary.TButton",
            command=dialog.destroy,
        ).pack(anchor="e", pady=(12, 0))

    def _update_summary_text(self, pending=False):
        parts = list(self._summary_base_parts or [])
        if pending:
            parts.append("Spelling check running...")
        else:
            rows = self.spell_issues.get("rows", {}) if isinstance(self.spell_issues, dict) else {}
            pages = self.spell_issues.get("pages", {}) if isinstance(self.spell_issues, dict) else {}
            if rows:
                row_total = sum(len(v) for v in rows.values())
                parts.append(f"Row spelling issues: {row_total} word{'s' if row_total != 1 else ''}")
            if pages:
                page_total = sum(len(v) for v in pages.values())
                parts.append(f"Page spelling issues: {page_total} word{'s' if page_total != 1 else ''}")
            elif self.spell_checker is False:
                parts.append("Spelling check unavailable (install pyspellchecker)")
        summary_text = " | ".join(parts)
        self.summary_var.set(summary_text)
        self._latest_summary_text = summary_text

    def _start_spellcheck(self, results, pos_analysis, job_id):
        self._pending_history = (
            copy.deepcopy(results),
            copy.deepcopy(pos_analysis) if pos_analysis else None,
        )
        checker = self._get_spell_checker()
        if checker is None:
            self._update_summary_text(pending=False)
            self._update_spell_button()
            self._populate_spell_tab({"rows": {}, "pages": {}})
            self._refresh_spell_column(pending=False)
            self._update_upload_button_state()
            if self._pending_history:
                res_copy, pos_copy = self._pending_history
                self._add_history_entry(self.current_file_display, self.summary_var.get(), res_copy, pos_copy)
                self._pending_history = None
            return

        self._active_spellcheck_job = job_id
        self._spell_last_completed_job = 0
        self._update_summary_text(pending=True)
        if getattr(self, "spell_button", None) is not None:
            self.spell_button.configure(text="Spelling check running...")
            self.spell_button.state(["disabled"])
        self._refresh_spell_column(pending=True)

        results_copy = copy.deepcopy(results)

        def worker():
            issues = self._spellcheck_rows(results_copy)
            self.after(0, lambda: self._on_spellcheck_complete(job_id, issues))

        self._spellcheck_thread = threading.Thread(target=worker, daemon=True)
        self._spellcheck_thread.start()
        self._update_upload_button_state()

    def _on_spellcheck_complete(self, job_id, issues):
        if job_id != self._analysis_job:
            return
        self.spell_issues = issues or {"rows": {}, "pages": {}}
        self._spell_last_completed_job = job_id
        self._update_spell_button()
        self._update_summary_text(pending=False)
        self._refresh_spell_column(pending=False)
        self._populate_spell_tab(self.spell_issues)
        if self._pending_history:
            res_copy, pos_copy = self._pending_history
            self._add_history_entry(self.current_file_display, self.summary_var.get(), res_copy, pos_copy)
            self._pending_history = None
        self._spellcheck_thread = None
        self._update_upload_button_state()
# --------- Table extraction via pdfplumber (and helpers) ----------
def extract_rows_with_plumber(path):
    if pdfplumber is None:
        return [], [], []
    rows = []
    snippets = []
    words_by_page = []
    seen = set()
    section_keywords = ["PROFILES", "PROFILE", "PLATES", "PLATE", "PINS", "PIN"]
    table_counter = 0

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

    measurement_priority = [
        (("LENGTH", "LENGTH (MM)", "LENGTHMM"), "length"),
        (("SIZE", "DIMENSION", "DIMENSIONS"), "size"),
    ]

    quantity_keywords = ("ITEM QTY", "ITEMQTY", "ITEM_QTY", "QTY", "QUANTITY", "Q'TY")

    def _find_measurement_index(header_row):
        for keywords, measure_type in measurement_priority:
            idx = _find_header_index(header_row, keywords)
            if idx is not None:
                return idx, measure_type
        return None, None

    try:
        with pdfplumber.open(path) as pdf:
            for page_idx, page in enumerate(pdf.pages, start=1):
                page_words = page.extract_words(
                    x_tolerance=1.5, y_tolerance=1.5, keep_blank_chars=False, use_text_flow=True
                ) or []
                words_by_page.append(page_words)
                page_text_upper = (page.extract_text() or "").upper()
                has_section_word = any(word in page_text_upper for word in section_keywords)
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
                        _header_matches(cell, section_keywords)
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
                            quantity_idx = _find_header_index(candidate, quantity_keywords)
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
                        desc_parts = []
                        for idx in range(desc_idx, measure_idx):
                            if idx == desc_idx:
                                desc_parts.append((cells[idx] or "").strip())
                            else:
                                part = (cells[idx] or "").strip()
                                if part:
                                    desc_parts.append(part)
                        if not desc_parts:
                            continue
                        description = " ".join(desc_parts)
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
                        quantity_display = None
                        quantity_value = None
                        quantity_text = None
                        if quantity_idx is not None and quantity_idx < len(cells):
                            quantity_raw = (cells[quantity_idx] or "").strip()
                            if quantity_raw:
                                quantity_text = quantity_raw
                                quantity_display = quantity_raw
                                qty_numbers = re.findall(
                                    r"[-+]?\d+(?:\.\d+)?", quantity_raw.replace(",", "")
                                )
                                if qty_numbers:
                                    try:
                                        quantity_value = float(qty_numbers[0])
                                    except ValueError:
                                        quantity_value = None
                        pos_value = pos_value_raw.replace(" ", "")
                        length_key = tuple(round(v, 6) for v in length_options)
                        thickness_display = None
                        thickness_value = None
                        if thickness_idx is not None and thickness_idx < len(cells):
                            thickness_token_raw = (cells[thickness_idx] or "").strip()
                            if thickness_token_raw:
                                thickness_display = thickness_token_raw
                                thickness_numbers = re.findall(
                                    r"[-+]?\d+(?:\.\d+)?", thickness_token_raw.replace(",", "")
                                )
                                if thickness_numbers:
                                    try:
                                        thickness_value = abs(float(thickness_numbers[0]))
                                    except ValueError:
                                        thickness_value = None
                        thickness_key = round(thickness_value, 6) if thickness_value is not None else None
                        if quantity_value is not None:
                            quantity_key = round(quantity_value, 6)
                        elif quantity_text:
                            quantity_key = quantity_text.strip().lower()
                        else:
                            quantity_key = None
                        key = (pos_value, description, length_key, measure_type, thickness_key, quantity_key)
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


def main():
    app = PDFQCApp()
    app.mainloop()


if __name__ == "__main__":
    main()
