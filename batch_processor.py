#!/usr/bin/env python3
"""
Batch PDF Drawing Processing Engine.
Enables concurrent verification of multiple drawing PDFs in directories
with aggregated metrics and consolidated reports.
"""

import logging
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any, Optional, Union

import qc_logic
import cli

logger = logging.getLogger("qc_batch")


class BatchProcessor:
    """
    Engine for scanning, executing, and aggregating quality control checks
    across batches of PDF drawings.
    """

    def __init__(
        self,
        config: Optional[Dict[str, Any]] = None,
        tolerance: Optional[float] = None,
        max_workers: int = 4
    ):
        self.config = config or qc_logic.load_config()
        self.tolerance = tolerance
        self.max_workers = max(1, max_workers)

    def discover_pdfs(self, root_dir: Union[str, Path], recursive: bool = True) -> List[Path]:
        """Discover all PDF files in directory (case-insensitive), sorted by path."""
        p = Path(root_dir)
        if not p.exists() or not p.is_dir():
            raise NotADirectoryError(f"Directory not found: {root_dir}")

        iterator = p.rglob("*") if recursive else p.iterdir()
        return sorted([f for f in iterator if f.is_file() and f.suffix.lower() == ".pdf"])

    def process_single(self, pdf_path: Path) -> Dict[str, Any]:
        """Process a single PDF and return file-level summary and item results."""
        try:
            results = cli.check_pdf(
                str(pdf_path),
                tolerance=self.tolerance,
                config=self.config
            )
            summary = qc_logic.CheckSummary.from_results(results)
            return {
                "file": str(pdf_path),
                "filename": pdf_path.name,
                "status": "success",
                "summary": summary,
                "results": results,
                "error": None
            }
        except Exception as err:
            logger.error("Error processing %s: %s", pdf_path, err)
            return {
                "file": str(pdf_path),
                "filename": pdf_path.name,
                "status": "error",
                "summary": qc_logic.CheckSummary(),
                "results": [],
                "error": str(err)
            }

    def process_batch(
        self,
        pdf_paths: List[Path]
    ) -> Dict[str, Any]:
        """Process multiple PDFs concurrently and aggregate results."""
        file_results = []
        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            future_to_path = {executor.submit(self.process_single, p): p for p in pdf_paths}
            for future in as_completed(future_to_path):
                file_results.append(future.result())

        # Sort results deterministically by filename and full path
        file_results.sort(key=lambda r: (r["filename"], r["file"]))

        total_files = len(file_results)
        success_files = sum(1 for r in file_results if r["status"] == "success")
        error_files = total_files - success_files

        total_bom_items = sum(r["summary"].total_items for r in file_results)
        total_passed = sum(r["summary"].passed for r in file_results)
        total_failed = sum(r["summary"].failed for r in file_results)
        overall_pass_rate = round((total_passed / total_bom_items * 100.0), 2) if total_bom_items > 0 else 0.0

        return {
            "total_files": total_files,
            "processed_successfully": success_files,
            "processing_errors": error_files,
            "total_bom_items": total_bom_items,
            "total_passed": total_passed,
            "total_failed": total_failed,
            "overall_pass_rate": overall_pass_rate,
            "files": file_results
        }

    def generate_consolidated_markdown(self, batch_report: Dict[str, Any]) -> str:
        """Create a markdown summary table for the entire batch."""
        def _esc(val: Any) -> str:
            return str(val).replace("\r\n", " ").replace("\n", " ").replace("|", "\\|")

        lines = [
            "# Batch PDF Drawing Quality Audit Report",
            "",
            (
                f"**Drawings Checked:** {batch_report['total_files']} | "
                f"**BOM Items Audited:** {batch_report['total_bom_items']} | "
                f"**Overall Pass Rate:** {batch_report['overall_pass_rate']}%"
            ),
            "",
            "| Drawing File | Items | Passed | Failed | Pass Rate | Status |",
            "| :--- | :--- | :--- | :--- | :--- | :--- |",
        ]

        for f in batch_report["files"]:
            name = _esc(f["filename"])
            if f["status"] == "error":
                err_msg = _esc(f["error"])
                lines.append(f"| {name} | 0 | 0 | 0 | 0.0% | ❌ Error ({err_msg}) |")
            else:
                s = f["summary"]
                if s.total_items == 0:
                    badge = "⚠️ EMPTY"
                elif s.failed == 0:
                    badge = "✅ PASS"
                else:
                    badge = "❌ FAIL"
                lines.append(f"| {name} | {s.total_items} | {s.passed} | {s.failed} | {s.pass_rate}% | {badge} |")

        lines.append("")
        return "\n".join(lines)
