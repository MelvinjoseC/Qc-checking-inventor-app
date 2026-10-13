import unittest
import qc_logic


class TestQCLogic(unittest.TestCase):
    def test_normalize_word_token(self):
        self.assertEqual(qc_logic.normalize_word_token("Hello!"), "hello")
        self.assertEqual(qc_logic.normalize_word_token("12.3mm"), "12.3mm")
        self.assertEqual(qc_logic.normalize_word_token("abc+-123"), "abc+-123")
        self.assertEqual(qc_logic.normalize_word_token(""), "")

    def test_pos_numeric_value(self):
        self.assertEqual(qc_logic._pos_numeric_value("10"), 10.0)
        self.assertEqual(qc_logic._pos_numeric_value("12.5"), 12.5)
        self.assertEqual(qc_logic._pos_numeric_value("abc"), None)
        self.assertEqual(qc_logic._pos_numeric_value(""), None)
        self.assertEqual(qc_logic._pos_numeric_value(None), None)

    def test_parse_table_row(self):
        # Valid table row with 'mm' ending
        row = qc_logic.parse_table_row("1 Plate Section A 1500 mm")
        self.assertIsNotNone(row)
        self.assertEqual(row["pos"], "1")
        self.assertEqual(row["description"], "Plate Section A")
        self.assertEqual(row["length"], 1500.0)
        self.assertEqual(row["length_display"], "1500 mm")

        # Valid table row with concatenated 'mm'
        row2 = qc_logic.parse_table_row("2.1 L-Bracket Plate 150.5mm")
        self.assertIsNotNone(row2)
        self.assertEqual(row2["pos"], "2.1")
        self.assertEqual(row2["description"], "L-Bracket Plate")
        self.assertEqual(row2["length"], 150.5)
        self.assertEqual(row2["length_display"], "150.5mm")


        # Invalid rows
        self.assertIsNone(qc_logic.parse_table_row("1 Plate Section A"))
        self.assertIsNone(qc_logic.parse_table_row("abc Plate Section A 150mm"))
        self.assertIsNone(qc_logic.parse_table_row("1 150mm"))  # missing description

    def test_normalize_token_variants(self):
        self.assertEqual(qc_logic._normalize_token_variants(None), [])
        self.assertEqual(qc_logic._normalize_token_variants([]), [])
        
        # Simple list of strings
        self.assertEqual(
            qc_logic._normalize_token_variants(["token1", "token2"]),
            [["token1", "token2"]]
        )
        
        # List of lists/tuples
        variants = [["a", "b"], "c", None, ["d"]]
        self.assertEqual(
            qc_logic._normalize_token_variants(variants),
            [["a", "b"], ["c"], ["d"]]
        )

    def test_match_callout_on_page(self):
        words = [
            {"text": "Pos", "x0": 10, "x1": 20, "top": 50, "bottom": 60},
            {"text": "1.0", "x0": 22, "x1": 35, "top": 50, "bottom": 60},
            {"text": "PLATE", "x0": 40, "x1": 80, "top": 50, "bottom": 60},
        ]
        
        # Exact match
        bbox = qc_logic._match_callout_on_page(["pos", "1.0"], words)
        self.assertIsNotNone(bbox)
        self.assertEqual(bbox["x0"], 10)
        self.assertEqual(bbox["x1"], 35)

        # No match
        bbox_fail = qc_logic._match_callout_on_page(["pos", "2.0"], words)
        self.assertIsNone(bbox_fail)

    def test_numeric_from_text(self):
        self.assertEqual(qc_logic._numeric_from_text("Ø50 L=120"), [50.0, 120.0])
        self.assertEqual(qc_logic._numeric_from_text("Plate 12.5 thk x 1500 mm"), [12.5, 1500.0])
        self.assertEqual(qc_logic._numeric_from_text("no numbers here"), [])

    def test_pick_candidate(self):
        candidates = [100.0, 120.0, 150.0]
        
        # Pick exact expected length
        val, mode = qc_logic._pick_candidate(candidates, 120.0)
        self.assertEqual(val, 120.0)
        self.assertEqual(mode, "closest_to_expected")

        # Pick closest to expected within tolerance
        val, mode = qc_logic._pick_candidate(candidates, 120.3, tolerance=0.5)
        self.assertEqual(val, 120.0)
        self.assertEqual(mode, "closest_to_expected")

        # No expected length: pick max candidate
        val, mode = qc_logic._pick_candidate(candidates, None)
        self.assertEqual(val, 150.0)
        self.assertEqual(mode, "max_in_window")

    def test_tokenize(self):
        self.assertEqual(qc_logic.tokenize("Hello, World 123!"), ["hello", "world", "123"])
        self.assertEqual(qc_logic.tokenize(""), [])

    def test_contains_subsequence(self):
        tokens = ["a", "b", "c", "d"]
        self.assertTrue(qc_logic.contains_subsequence(tokens, ["b", "c"]))
        self.assertFalse(qc_logic.contains_subsequence(tokens, ["b", "d"]))
        self.assertFalse(qc_logic.contains_subsequence(tokens, []))

    def test_extract_numeric_values(self):
        self.assertEqual(qc_logic.extract_numeric_values("Qty 2, length 1,234.5 mm"), [2.0, 1234.5])
        self.assertEqual(qc_logic.extract_numeric_values("no digits"), [])

    def test_format_length(self):
        self.assertEqual(qc_logic.format_length(150.0), "150 mm")
        self.assertEqual(qc_logic.format_length(150.54321), "150.543 mm")

    def test_remove_table_snippets_from_pages(self):
        page_texts = [
            "This is drawing text\nPOS DESCRIPTION LENGTH\n1 Plate A 1500 mm\nEnd of page 1",
            "This is page 2\nPOS DESCRIPTION LENGTH\n2 Pin B 50 mm\nEnd of page 2"
        ]
        snippets = [
            (1, "1 Plate A 1500 mm"),
            (2, "2 Pin B 50 mm")
        ]
        cleaned = qc_logic.remove_table_snippets_from_pages(page_texts, snippets)
        self.assertEqual(len(cleaned), 2)
        self.assertNotIn("1 Plate A 1500 mm", cleaned[0])
        self.assertNotIn("2 Pin B 50 mm", cleaned[1])
        self.assertIn("This is drawing text", cleaned[0])

    def test_text_extraction_edge_cases(self):
        # Non-existent file should raise PDFQCError
        with self.assertRaises(qc_logic.PDFQCError):
            qc_logic.extract_text_from_pdf("non_existent_file.pdf")
            
        with self.assertRaises(qc_logic.PDFQCError):
            qc_logic.extract_page_texts("non_existent_file.pdf")

    def test_plumber_row_parsing_helpers(self):
        cells = ["10", "Plate A", "Extra Info", "1500 mm", "12 mm", "2"]
        desc = qc_logic._parse_row_description(cells, 1, 3)
        self.assertEqual(desc, "Plate A Extra Info")

        thk_val, thk_disp = qc_logic._parse_row_thickness(cells, 4)
        self.assertEqual(thk_val, 12.0)
        self.assertEqual(thk_disp, "12 mm")

        qty_val, qty_disp = qc_logic._parse_row_quantity(cells, 5)
        self.assertEqual(qty_val, 2.0)
        self.assertEqual(qty_disp, "2")

        key = qc_logic._generate_row_key("10", "Plate A Extra Info", [1500.0], "length", 12.0, 2.0, "2")
        self.assertEqual(key, ("10", "Plate A Extra Info", (1500.0,), "length", 12.0, 2.0))

        # Test index detection helpers
        header = ["POS", "DESCRIPTION", "LENGTH", "QTY"]
        self.assertEqual(qc_logic._find_header_index(header, ["POS"]), 0)
        self.assertEqual(qc_logic._find_header_index(header, ["DESCRIPTION"]), 1)
        self.assertEqual(qc_logic._find_header_index(header, ["LENGTH"]), 2)
        self.assertEqual(qc_logic._find_header_index(header, ["QTY"]), 3)

        measure_idx, measure_type = qc_logic._find_measurement_index(header)
        self.assertEqual(measure_idx, 2)
        self.assertEqual(measure_type, "length")

    def test_validate_config(self):
        # Test with valid config
        valid = {
            "tolerance": 0.8,
            "default_dpi": 150,
            "poppler_path": "/usr/bin/poppler",
            "tesseract_path": "/usr/bin/tesseract"
        }
        res = qc_logic.validate_config(valid)
        self.assertEqual(res["tolerance"], 0.8)
        self.assertEqual(res["default_dpi"], 150)
        self.assertEqual(res["poppler_path"], "/usr/bin/poppler")
        self.assertEqual(res["tesseract_path"], "/usr/bin/tesseract")

        # Test with invalid formats
        invalid = {
            "tolerance": "abc",
            "default_dpi": "not-an-int",
            "poppler_path": 123
        }
        res2 = qc_logic.validate_config(invalid)
        self.assertEqual(res2["tolerance"], 0.5)  # default fallback
        self.assertEqual(res2["default_dpi"], 300) # default fallback
        self.assertEqual(res2["poppler_path"], "123") # converted to string

    def test_config_load_save(self):
        import os
        test_config_path = "test_config.json"
        try:
            cfg = {"tolerance": 0.8, "default_dpi": 150}
            self.assertTrue(qc_logic.save_config(cfg, path=test_config_path))
            loaded = qc_logic.load_config(path=test_config_path)
            self.assertEqual(loaded["tolerance"], 0.8)
            self.assertEqual(loaded["default_dpi"], 150)
            self.assertEqual(loaded["poppler_path"], "")
        finally:
            if os.path.exists(test_config_path):
                os.remove(test_config_path)

    def test_load_spellcheck_allowlist(self):
        import os
        test_file = "test_allowlist.txt"
        try:
            with open(test_file, "w", encoding="utf-8") as f:
                f.write("customword1\n# commentedword\nCUSTOMWORD2\n")
            words = qc_logic.load_spellcheck_allowlist(path=test_file)
            self.assertIn("customword1", words)
            self.assertIn("customword2", words)
            self.assertNotIn("commentedword", words)
        finally:
            if os.path.exists(test_file):
                os.remove(test_file)

    def test_export_to_csv(self):
        results = [
            {
                "pos": "1",
                "description": "Plate Section",
                "status": "PASS",
                "quantity": 2.0,
                "quantity_display": "2",
                "length": 150.0,
                "length_display": "150 mm",
                "length_found": True,
                "drawing_length": 150.0,
                "length_match": True,
                "thickness": 12.0,
                "thickness_display": "12 mm",
                "thickness_found": True,
                "drawing_thickness": 12.0,
                "thickness_match": True,
                "details": "Matched on page 1"
            }
        ]
        csv_str = qc_logic.export_to_csv(results)
        self.assertIn("POS,Description,Status", csv_str)
        self.assertIn("1,Plate Section,PASS", csv_str)
        self.assertIn("150 mm,150.0,Yes", csv_str)

    def test_export_to_csv_custom_columns(self):
        results = [
            {
                "pos": "1",
                "description": "Plate Section",
                "status": "PASS"
            }
        ]
        csv_str = qc_logic.export_to_csv(results, columns=["pos", "status"])
        self.assertIn("POS,Status", csv_str)
        self.assertNotIn("Description", csv_str)
        self.assertIn("1,PASS", csv_str)

    def test_export_to_json(self):
        results = [
            {
                "pos": "1",
                "description": "Plate Section",
                "status": "PASS"
            }
        ]
        json_str = qc_logic.export_to_json(results)
        self.assertIn('"pos": "1"', json_str)
        self.assertIn('"description": "Plate Section"', json_str)
        self.assertIn('"status": "PASS"', json_str)

    def test_domain_models_dataclass(self):
        anchor = qc_logic.TableAnchor(x0=10.0, x1=20.0, top=30.0, bottom=40.0)
        self.assertEqual(anchor.to_dict(), {"x0": 10.0, "x1": 20.0, "top": 30.0, "bottom": 40.0})
        restored_anchor = qc_logic.TableAnchor.from_dict({"x0": 10.0, "x1": 20.0, "top": 30.0, "bottom": 40.0})
        self.assertEqual(restored_anchor.top, 30.0)
        self.assertIsNone(qc_logic.TableAnchor.from_dict(None))

        item = qc_logic.BOMItem(
            pos="10",
            description="Beam Section",
            length=1200.0,
            length_display="1200 mm",
            quantity=2.0,
            table_anchor=anchor
        )
        item_dict = item.to_dict()
        self.assertEqual(item_dict["pos"], "10")
        self.assertEqual(item_dict["table_anchor"]["x0"], 10.0)

        restored_item = qc_logic.BOMItem.from_dict(item_dict)
        self.assertEqual(restored_item.pos, "10")
        self.assertEqual(restored_item.description, "Beam Section")
        self.assertEqual(restored_item.length, 1200.0)

        res = qc_logic.QCValidationResult(
            pos="10",
            description="Beam Section",
            status=qc_logic.QCStatus.PASS.value,
            length=1200.0,
            drawing_length=1200.0,
            length_match=True
        )
        res_dict = res.to_dict()
        self.assertEqual(res_dict["status"], "PASS")
        self.assertTrue(res_dict["length_match"])
        restored_res = qc_logic.QCValidationResult.from_dict(res_dict)
        self.assertEqual(restored_res.status, "PASS")

    def test_check_summary_aggregation(self):
        results = [
            qc_logic.QCValidationResult(pos="1", description="Part 1", status=qc_logic.QCStatus.PASS.value),
            qc_logic.QCValidationResult(pos="2", description="Part 2", status=qc_logic.QCStatus.FAIL.value),
            qc_logic.QCValidationResult(pos="3", description="Part 3", status=qc_logic.QCStatus.WARNING.value),
            qc_logic.QCValidationResult(pos="4", description="Part 4", status=qc_logic.QCStatus.PASS.value),
        ]
        summary = qc_logic.CheckSummary.from_results(results)
        self.assertEqual(summary.total_items, 4)
        self.assertEqual(summary.passed, 2)
        self.assertEqual(summary.failed, 1)
        self.assertEqual(summary.warnings, 1)
        self.assertEqual(summary.pass_rate, 50.0)

        # Empty results edge case
        empty_summary = qc_logic.CheckSummary.from_results([])
        self.assertEqual(empty_summary.total_items, 0)
        self.assertEqual(empty_summary.pass_rate, 0.0)

    def test_convert_dimension(self):
        # mm to cm, m
        self.assertEqual(qc_logic.convert_dimension(100.0, "mm", "cm"), 10.0)
        self.assertEqual(qc_logic.convert_dimension(1500.0, "mm", "m"), 1.5)
        # m, cm to mm
        self.assertEqual(qc_logic.convert_dimension(2.5, "m", "mm"), 2500.0)
        self.assertEqual(qc_logic.convert_dimension(12.0, "cm", "mm"), 120.0)
        # in to mm (1 in = 25.4 mm)
        self.assertEqual(qc_logic.convert_dimension(2.0, "in", "mm"), 50.8)
        self.assertEqual(qc_logic.convert_dimension(1.0, '"', "mm"), 25.4)
        # ft to mm (1 ft = 304.8 mm)
        self.assertEqual(qc_logic.convert_dimension(1.0, "ft", "mm"), 304.8)

        # Invalid units
        with self.assertRaises(ValueError):
            qc_logic.convert_dimension(10.0, "yards", "mm")
        with self.assertRaises(ValueError):
            qc_logic.convert_dimension(10.0, "mm", "lightyears")

    def test_parse_dimension_string(self):
        # Metric
        val, disp = qc_logic.parse_dimension_string("150 mm")
        self.assertEqual(val, 150.0)
        self.assertEqual(disp, "150 mm")

        val_m, _ = qc_logic.parse_dimension_string("1.5 m")
        self.assertEqual(val_m, 1500.0)

        # Fractional imperial
        val_half, _ = qc_logic.parse_dimension_string('1/2"')
        self.assertEqual(val_half, 12.7)

        val_mixed, _ = qc_logic.parse_dimension_string('2-1/2"')
        self.assertEqual(val_mixed, 63.5)

        val_space, _ = qc_logic.parse_dimension_string('2 1/2 in')
        self.assertEqual(val_space, 63.5)

        val_three_quarter, _ = qc_logic.parse_dimension_string("3/4 in")
        self.assertEqual(val_three_quarter, 19.05)

        # Invalid or empty
        self.assertEqual(qc_logic.parse_dimension_string(""), (None, None))
        self.assertEqual(qc_logic.parse_dimension_string("invalid string"), (None, None))
        self.assertEqual(qc_logic.parse_dimension_string("1/0 in"), (None, None))

    def test_is_within_tolerance(self):
        # Absolute tolerance
        self.assertTrue(qc_logic.is_within_tolerance(100.2, 100.0, tolerance=0.5))
        self.assertFalse(qc_logic.is_within_tolerance(100.6, 100.0, tolerance=0.5))

        # Percentage tolerance: 100 ± 2% -> 98 to 102
        self.assertTrue(qc_logic.is_within_tolerance(101.5, 100.0, tolerance=2.0, mode=qc_logic.ToleranceMode.PERCENTAGE))
        self.assertFalse(qc_logic.is_within_tolerance(103.0, 100.0, tolerance=2.0, mode=qc_logic.ToleranceMode.PERCENTAGE))
        # Zero expected
        self.assertTrue(qc_logic.is_within_tolerance(0.0, 0.0, tolerance=1.0, mode=qc_logic.ToleranceMode.PERCENTAGE))

    def test_pick_candidate_percentage_tolerance(self):
        candidates = [98.5, 120.0]
        # With percentage tolerance of 2%, 98.5 is within 2% of 100.0
        val, mode = qc_logic._pick_candidate(
            candidates, 100.0, prefer_max=True, tolerance=2.0, tolerance_mode=qc_logic.ToleranceMode.PERCENTAGE
        )
        self.assertEqual(val, 98.5)
        self.assertEqual(mode, "match_expected")

    def test_generate_pos_callout_variants(self):
        # For numeric POS '1'
        variants = qc_logic.generate_pos_callout_variants("1")
        self.assertIn(["1"], variants)
        self.assertIn(["pos", "1"], variants)
        self.assertIn(["pos1"], variants)
        self.assertIn(["item", "1"], variants)
        self.assertIn(["p1"], variants)
        self.assertIn(["mk", "1"], variants)

        # For decimal POS '2.0' -> should include both '2.0' and '2'
        variants_dec = qc_logic.generate_pos_callout_variants("2.0")
        self.assertIn(["2.0"], variants_dec)
        self.assertIn(["2"], variants_dec)
        self.assertIn(["pos", "2"], variants_dec)

        # Empty POS
        self.assertEqual(qc_logic.generate_pos_callout_variants(""), [])

    def test_export_to_html(self):
        results = [
            {
                "pos": "1",
                "description": "Base <Plate> & Flange",
                "status": "PASS",
                "quantity": 1.0,
                "quantity_display": "1",
                "length": 500.0,
                "length_display": "500 mm",
                "length_found": True,
                "drawing_length": 500.0,
                "length_match": True,
                "thickness": 10.0,
                "thickness_display": "10 mm",
                "thickness_found": True,
                "drawing_thickness": 10.0,
                "thickness_match": True,
                "details": "Callout verified"
            },
            {
                "pos": "2",
                "description": "Support Angle",
                "status": "FAIL",
                "length_match": False,
                "details": "Length mismatch"
            }
        ]
        html_out = qc_logic.export_to_html(results, title="Fabrication Audit Report")
        self.assertIn("<!DOCTYPE html>", html_out)
        self.assertIn("Fabrication Audit Report", html_out)
        self.assertIn("Total Items", html_out)
        self.assertIn("Pass Rate", html_out)
        # Verify HTML escaping
        self.assertIn("Base &lt;Plate&gt; &amp; Flange", html_out)
        self.assertIn("badge-success", html_out)
        self.assertIn("badge-danger", html_out)


if __name__ == "__main__":
    unittest.main()




