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


if __name__ == "__main__":
    unittest.main()
