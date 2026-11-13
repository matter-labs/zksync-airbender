"""Regressions for the native decoder row differential."""
import copy
import struct
import unittest
import io
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch
import check_program_decoder_rows as decoder
from check_program_decoder_rows import checked_rows, SMALL_PROGRAMS, check_group_shapes, csr_word

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

    def test_blake_group_shape(self):
        valid = b"".join(struct.pack("<I", word) for word in SMALL_PROGRAMS["blake-caller"])
        check_group_shapes(valid, "reduced", "valid caller")
        with self.assertRaisesRegex(ValueError, "length 1"):
            check_group_shapes(struct.pack("<II", csr_word(0x7C7), 0x13),
                               "reduced", "broken caller")

    def test_split_group_shape(self):
        words = SMALL_PROGRAMS["split-keccak"]
        check_group_shapes(b"".join(struct.pack("<I", word) for word in words),
                           "full", "valid split")
        changed = words[:8] + (csr_word(0x7CD),) + words[9:]
        with self.assertRaisesRegex(ValueError, "invalid split Keccak"):
            check_group_shapes(b"".join(struct.pack("<I", word) for word in changed),
                               "full", "broken split")


class DecoderFixtureInventoryTest(unittest.TestCase):
    def test_all_126_cases_are_retained(self):
        cases = []
        def record(exporter, oracle, directory, text, image, config, family, cache):
            cases.append((text.stem, config, family, cache))
            return 'a' * 64
        arguments = ['decoder', '--exporter', '/unused/exporter', '--oracle', '/unused/oracle']
        def run(extra):
            cases.clear()
            with patch.object(sys, 'argv', arguments + extra), patch.object(decoder, 'run_case', record), \
                    patch('sys.stdout', new_callable=io.StringIO):
                decoder.main()
            return len(cases)
        self.assertEqual(run([]), 90)
        self.assertEqual(run(['--committed-verifiers']), 22)
        with tempfile.TemporaryDirectory() as directory:
            text = Path(directory) / 'multiblock_batch.text'
            text.write_bytes(struct.pack('<I', 0x13))
            text.with_suffix('.bin').write_bytes(text.read_bytes())
            self.assertEqual(run(['--program', str(text), '--configs', 'full,unified']), 14)


if __name__ == '__main__':
    unittest.main()
