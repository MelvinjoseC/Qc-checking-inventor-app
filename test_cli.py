import unittest
from unittest.mock import patch, MagicMock
import os
import tempfile
from pathlib import Path

import cli
import qc_logic


class TestCLI(unittest.TestCase):
    def test_parser_defaults(self):
        parser = cli.build_parser()
        args = parser.parse_args(["test_drawing.pdf"])
        self.assertEqual(args.pdf_path, "test_drawing.pdf")
        self.assertEqual(args.format, "summary")
        self.assertEqual(args.config, "config.json")
        self.assertIsNone(args.tolerance)
        self.assertIsNone(args.output)
        self.assertFalse(args.strict)
        self.assertFalse(args.verbose)

    def test_parser_custom_args(self):
        parser = cli.build_parser()
        args = parser.parse_args([
            "drawing.pdf",
            "-c", "custom_config.json",
            "-t", "1.5",
            "-f", "html",
            "-o", "report.html",
            "--strict",
            "-v"
        ])
        self.assertEqual(args.pdf_path, "drawing.pdf")
        self.assertEqual(args.config, "custom_config.json")
        self.assertEqual(args.tolerance, 1.5)
        self.assertEqual(args.format, "html")
        self.assertEqual(args.output, "report.html")
        self.assertTrue(args.strict)
        self.assertTrue(args.verbose)

    def test_main_file_not_found(self):
        exit_code = cli.main(["non_existent_file.pdf"])
        self.assertEqual(exit_code, 2)

    @patch("cli.check_pdf")
    def test_main_summary_output(self, mock_check_pdf):
        mock_check_pdf.return_value = [
            {
                "pos": "1",
                "description": "Plate",
                "status": "PASS",
                "quantity": 1.0,
                "quantity_display": "1",
                "length": 100.0,
                "length_display": "100 mm",
                "length_found": True,
                "drawing_length": 100.0,
                "length_match": True,
                "thickness": 10.0,
                "thickness_display": "10 mm",
                "thickness_found": True,
                "drawing_thickness": 10.0,
                "thickness_match": True,
                "details": "Verified",
                "page": 1
            }
        ]
        with patch("builtins.print") as mock_print:
            exit_code = cli.main(["dummy.pdf", "-f", "summary"])
            self.assertEqual(exit_code, 0)
            mock_print.assert_called()

    @patch("cli.check_pdf")
    def test_main_strict_mode_fail(self, mock_check_pdf):
        mock_check_pdf.return_value = [
            {
                "pos": "1",
                "description": "Plate",
                "status": "FAIL",
                "quantity": 1.0,
                "quantity_display": "1",
                "length": 100.0,
                "length_display": "100 mm",
                "length_found": False,
                "drawing_length": None,
                "length_match": False,
                "thickness": None,
                "thickness_display": None,
                "thickness_found": False,
                "drawing_thickness": None,
                "thickness_match": False,
                "details": "Missing",
                "page": None
            }
        ]
        exit_code = cli.main(["dummy.pdf", "--strict"])
        self.assertEqual(exit_code, 1)

    @patch("cli.check_pdf")
    def test_main_file_output_json(self, mock_check_pdf):
        mock_check_pdf.return_value = [
            {
                "pos": "1",
                "description": "Plate",
                "status": "PASS",
                "quantity": 1.0,
                "quantity_display": "1",
                "length": 100.0,
                "length_display": "100 mm",
                "length_found": True,
                "drawing_length": 100.0,
                "length_match": True,
                "thickness": None,
                "thickness_display": None,
                "thickness_found": False,
                "drawing_thickness": None,
                "thickness_match": False,
                "details": "Verified",
                "page": 1
            }
        ]
        with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as tmp:
            tmp_path = tmp.name

        try:
            exit_code = cli.main(["dummy.pdf", "-f", "json", "-o", tmp_path])
            self.assertEqual(exit_code, 0)
            with open(tmp_path, "r", encoding="utf-8") as f:
                content = f.read()
            self.assertIn('"pos": "1"', content)
        finally:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)


if __name__ == "__main__":
    unittest.main()
