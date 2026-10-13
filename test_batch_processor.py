import unittest
from unittest.mock import patch
import os
import tempfile
from pathlib import Path

from batch_processor import BatchProcessor
import qc_logic


class TestBatchProcessor(unittest.TestCase):
    def setUp(self):
        self.processor = BatchProcessor(tolerance=0.5, max_workers=2)

    def test_discover_pdfs(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            base = Path(tmp_dir)
            (base / "drawing1.pdf").touch()
            (base / "drawing2.pdf").touch()
            (base / "notes.txt").touch()
            sub = base / "subfolder"
            sub.mkdir()
            (sub / "drawing3.pdf").touch()

            # Recursive discovery
            discovered = self.processor.discover_pdfs(base, recursive=True)
            self.assertEqual(len(discovered), 3)

            # Non-recursive discovery
            discovered_shallow = self.processor.discover_pdfs(base, recursive=False)
            self.assertEqual(len(discovered_shallow), 2)

    def test_discover_pdfs_invalid_dir(self):
        with self.assertRaises(NotADirectoryError):
            self.processor.discover_pdfs("non_existent_folder_12345")

    @patch("cli.check_pdf")
    def test_process_batch_aggregation(self, mock_check_pdf):
        # File 1 passes
        # File 2 has 1 pass and 1 fail
        mock_check_pdf.side_effect = [
            [
                {"pos": "1", "description": "Plate", "status": "PASS"}
            ],
            [
                {"pos": "1", "description": "Angle", "status": "PASS"},
                {"pos": "2", "description": "Bracket", "status": "FAIL"}
            ]
        ]

        paths = [Path("drawingA.pdf"), Path("drawingB.pdf")]
        batch_res = self.processor.process_batch(paths)

        self.assertEqual(batch_res["total_files"], 2)
        self.assertEqual(batch_res["processed_successfully"], 2)
        self.assertEqual(batch_res["processing_errors"], 0)
        self.assertEqual(batch_res["total_bom_items"], 3)
        self.assertEqual(batch_res["total_passed"], 2)
        self.assertEqual(batch_res["total_failed"], 1)
        self.assertEqual(batch_res["overall_pass_rate"], 66.67)

    @patch("cli.check_pdf")
    def test_process_batch_with_error(self, mock_check_pdf):
        mock_check_pdf.side_effect = Exception("Corrupt PDF header")

        paths = [Path("corrupt.pdf")]
        batch_res = self.processor.process_batch(paths)

        self.assertEqual(batch_res["total_files"], 1)
        self.assertEqual(batch_res["processed_successfully"], 0)
        self.assertEqual(batch_res["processing_errors"], 1)
        self.assertEqual(batch_res["overall_pass_rate"], 0.0)
        self.assertIn("Corrupt PDF header", batch_res["files"][0]["error"])

    def test_generate_consolidated_markdown(self):
        report_data = {
            "total_files": 1,
            "total_bom_items": 2,
            "overall_pass_rate": 100.0,
            "files": [
                {
                    "filename": "assembly1.pdf",
                    "status": "success",
                    "summary": qc_logic.CheckSummary(total_items=2, passed=2, failed=0, pass_rate=100.0),
                    "error": None
                }
            ]
        }
        md = self.processor.generate_consolidated_markdown(report_data)
        self.assertIn("# Batch PDF Drawing Quality Audit Report", md)
        self.assertIn("assembly1.pdf", md)
        self.assertIn("✅ PASS", md)


if __name__ == "__main__":
    unittest.main()
