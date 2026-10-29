import copy
import unittest

from check_program_decoder_rows import checked_rows


class ProgramDecoderRowsTest(unittest.TestCase):
    def setUp(self):
        sentinel = 2013265920
        self.artifact = {
            "field_modulus": 2013265921,
            "trace_len": 4,
            "program": {"text_words": 4},
            "circuit": {
                "decode_table_columns_mask": [True, True] + [False] * 7,
                "tables_ids_in_generic_lookups": False,
                "offset_for_decoder_table": 0,
                "total_tables_size": 4,
            },
            "columns": [
                {"blocks": [{"kind": "dense", "values": [0, 4]},
                            {"kind": "affine", "length": 2, "first": sentinel, "step": 0}]},
                {"blocks": [{"kind": "dense", "values": [0, 0, sentinel, sentinel]}]},
            ],
        }
        self.active = {0: [0, 0], 1: [4, 0]}

    def test_exact_active_and_sentinel_rows(self):
        checked_rows(self.artifact, self.active, "control")

    def test_changed_active_value_rejected(self):
        changed = copy.deepcopy(self.artifact)
        changed["columns"][0]["blocks"][0]["values"][1] = 8
        with self.assertRaisesRegex(ValueError, "decoder row 1"):
            checked_rows(changed, self.active, "changed active")

    def test_changed_sentinel_rejected(self):
        changed = copy.deepcopy(self.artifact)
        changed["columns"][0]["blocks"][1]["first"] = 0
        with self.assertRaisesRegex(ValueError, "non-sentinel padding"):
            checked_rows(changed, self.active, "changed sentinel")

    def test_changed_mask_rejected(self):
        with self.assertRaisesRegex(ValueError, "differs from imported Lean mask"):
            checked_rows(self.artifact, self.active, "changed mask", [True] * 9)


if __name__ == "__main__":
    unittest.main()
