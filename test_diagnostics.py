import unittest
from unittest.mock import patch, MagicMock
from pathlib import Path

import diagnostics


class TestDiagnostics(unittest.TestCase):
    def test_check_python_module_existing(self):
        # 'sys' and 'unittest' should always exist
        res = diagnostics.check_python_module("unittest")
        self.assertTrue(res["available"])
        self.assertEqual(res["name"], "unittest")
        self.assertIsNone(res["error"])

    def test_check_python_module_nonexistent(self):
        res = diagnostics.check_python_module("non_existent_module_9999")
        self.assertFalse(res["available"])
        self.assertIsNotNone(res["error"])

    @patch("shutil.which")
    def test_check_binary_not_found(self, mock_which):
        mock_which.return_value = None
        res = diagnostics.check_binary("missing_bin")
        self.assertFalse(res["found"])
        self.assertIsNone(res["path"])

    @patch("shutil.which")
    @patch("subprocess.run")
    def test_check_binary_found(self, mock_run, mock_which):
        mock_which.return_value = "/usr/bin/mock_bin"
        mock_run.return_value = MagicMock(returncode=0, stdout="mock_bin version 1.0.0\n")
        res = diagnostics.check_binary("mock_bin")
        self.assertTrue(res["found"])
        self.assertEqual(res["path"], "/usr/bin/mock_bin")
        self.assertIn("1.0.0", res["version"])

    @patch("diagnostics.check_binary")
    @patch("diagnostics.check_python_module")
    def test_run_system_diagnostics(self, mock_check_module, mock_check_binary):
        mock_check_module.return_value = {"name": "dummy", "available": True, "version": "1.0", "error": None}
        mock_check_binary.return_value = {"name": "dummy", "found": True, "path": "/bin/dummy", "version": "1.0"}

        report = diagnostics.run_system_diagnostics()
        self.assertIn("python_version", report)
        self.assertIn("platform", report)
        self.assertTrue(report["all_required_ok"])
        self.assertTrue(report["ocr_ready"])

        formatted = diagnostics.format_diagnostics_report(report)
        self.assertIn("PDF DRAWING CHECKER SYSTEM DIAGNOSTICS", formatted)
        self.assertIn("[READY]", formatted)


if __name__ == "__main__":
    unittest.main()
