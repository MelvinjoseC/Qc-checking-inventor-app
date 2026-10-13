#!/usr/bin/env python3
"""
Command-Line Interface (CLI) for PDF Drawing Checker.
Enables headless verification of fabrication drawing PDFs in CI/CD pipelines
and terminal workflows.
"""

import sys
import os
import argparse
import logging
from pathlib import Path
from typing import List, Optional, Dict, Any

import qc_logic

logger = logging.getLogger("qc_cli")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="qc-checker",
        description="Headless PDF Drawing Quality Control and BOM Cross-Referencing Tool"
    )
    parser.add_argument(
        "pdf_path",
        help="Path to the PDF drawing file to check"
    )
    parser.add_argument(
        "--config", "-c",
        default="config.json",
        help="Path to configuration JSON file (default: config.json)"
    )
    parser.add_argument(
        "--tolerance", "-t",
        type=float,
        default=None,
        help="Measurement tolerance in mm (overrides config tolerance)"
    )
    parser.add_argument(
        "--format", "-f",
        choices=["summary", "csv", "json", "html", "markdown"],
        default="summary",
        help="Output format (default: summary)"
    )
    parser.add_argument(
        "--output", "-o",
        default=None,
        help="File path to write results to (prints to stdout if omitted)"
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit with non-zero code (1) if any BOM items fail verification"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Enable verbose DEBUG level logging"
    )
    return parser


def check_pdf(
    pdf_path: str,
    config_path: str = "config.json",
    tolerance: Optional[float] = None
) -> List[Dict[str, Any]]:
    """
    Run the core table extraction and callout matching algorithm on a PDF file.
    """
    path_obj = Path(pdf_path)
    if not path_obj.exists():
        raise FileNotFoundError(f"PDF file not found: {pdf_path}")

    config = qc_logic.load_config(config_path)
    if tolerance is not None:
        config["tolerance"] = float(tolerance)

    tol = config.get("tolerance", 0.5)

    # 1. Extract BOM rows and sheet text
    rows, snippets, words_by_page = qc_logic.extract_rows_with_plumber(str(path_obj))
    page_texts = qc_logic.extract_page_texts(str(path_obj))
    cleaned_pages = qc_logic.remove_table_snippets_from_pages(page_texts, snippets)

    results: List[Dict[str, Any]] = []

    for row in rows:
        pos = row.get("pos", "")
        desc = row.get("description", "")
        bom_len = row.get("length")
        bom_thk = row.get("thickness")
        qty = row.get("quantity")
        qty_display = row.get("quantity_display")

        callout_variants = qc_logic.generate_pos_callout_variants(pos)

        matched_page = None
        for page_idx, words in enumerate(words_by_page, start=1):
            for variant in callout_variants:
                bbox = qc_logic._match_callout_on_page(variant, words)
                if bbox:
                    matched_page = page_idx
                    break
            if matched_page:
                break

        drawing_len = None
        len_match = False
        drawing_thk = None
        thk_match = False

        if matched_page and matched_page <= len(cleaned_pages):
            page_content = cleaned_pages[matched_page - 1]
            numbers = qc_logic._numeric_from_text(page_content)
            if bom_len is not None and numbers:
                candidate, _ = qc_logic._pick_candidate(numbers, bom_len, tolerance=tol)
                if candidate is not None:
                    drawing_len = candidate
                    len_match = qc_logic.is_within_tolerance(candidate, bom_len, tolerance=tol)

            if bom_thk is not None and numbers:
                thk_cand, _ = qc_logic._pick_candidate(numbers, bom_thk, tolerance=tol)
                if thk_cand is not None:
                    drawing_thk = thk_cand
                    thk_match = qc_logic.is_within_tolerance(thk_cand, bom_thk, tolerance=tol)

        # Status determination
        if matched_page and (len_match or bom_len is None) and (thk_match or bom_thk is None):
            status = qc_logic.QCStatus.PASS.value
            details = f"Verified on sheet {matched_page}"
        elif matched_page:
            status = qc_logic.QCStatus.FAIL.value
            details = f"Callout found on sheet {matched_page}, but dimension mismatch"
        else:
            status = qc_logic.QCStatus.FAIL.value
            details = "Callout not found on drawing sheets"

        item_result = {
            "pos": pos,
            "description": desc,
            "status": status,
            "quantity": qty,
            "quantity_display": qty_display,
            "length": bom_len,
            "length_display": row.get("length_display"),
            "length_found": drawing_len is not None,
            "drawing_length": drawing_len,
            "length_match": len_match,
            "thickness": bom_thk,
            "thickness_display": row.get("thickness_display"),
            "thickness_found": drawing_thk is not None,
            "drawing_thickness": drawing_thk,
            "thickness_match": thk_match,
            "details": details,
            "page": matched_page
        }
        results.append(item_result)

    return results


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(level=log_level, format="%(levelname)s: %(message)s")

    try:
        results = check_pdf(args.pdf_path, config_path=args.config, tolerance=args.tolerance)
    except FileNotFoundError as err:
        logger.error(str(err))
        return 2
    except Exception as exc:
        logger.error("QC check failed with error: %s", exc)
        return 2

    summary = qc_logic.CheckSummary.from_results(results)

    output_str = ""
    if args.format == "csv":
        output_str = qc_logic.export_to_csv(results)
    elif args.format == "json":
        output_str = qc_logic.export_to_json(results)
    elif args.format == "html":
        output_str = qc_logic.export_to_html(results, title=f"QC Report - {Path(args.pdf_path).name}")
    elif args.format == "markdown":
        output_str = qc_logic.export_to_markdown(results, title=f"QC Report - {Path(args.pdf_path).name}")
    else:
        # Default summary format
        lines = [
            f"Drawing: {args.pdf_path}",
            f"Total BOM Items: {summary.total_items}",
            f"Passed:          {summary.passed}",
            f"Failed:          {summary.failed}",
            f"Pass Rate:       {summary.pass_rate}%",
            "-" * 40,
        ]
        for r in results:
            lines.append(f"[{r['status']}] POS {r['pos']}: {r['description']} -> {r['details']}")
        output_str = "\n".join(lines)

    if args.output:
        try:
            with open(args.output, "w", encoding="utf-8") as f:
                f.write(output_str)
            logger.info("Report written to %s", args.output)
        except Exception as write_err:
            logger.error("Failed to write output file: %s", write_err)
            return 2
    else:
        print(output_str)

    if args.strict and summary.failed > 0:
        return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())
