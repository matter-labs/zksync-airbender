"""Regressions for the native decoder row differential."""
import copy
import struct
import unittest
import io
import sys
import tempfile
import json
import subprocess
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
            return set(cases)
        small = run([])
        expected_small = {
            (program, config, family, cache)
            for program in SMALL_PROGRAMS
            for config, families in [('full', decoder.POOLED_FAMILIES),
                                     ('reduced', decoder.REDUCED_FAMILIES),
                                     ('unified', ('unified',))]
            for family in families for cache in ('plain', 'cached')
            if program != 'split-keccak' or (config == 'full' and family == 'add-sub')
        }
        self.assertEqual(small, expected_small)
        self.assertEqual(len(small), 90)
        committed = run(['--committed-verifiers'])
        repository = Path(__file__).resolve().parents[3]
        expected_committed = {
            (text.stem, config, family, cache)
            for text in (repository / 'tools/gkr_verifier').glob('fsv_*.text')
            for config, families in [('reduced', decoder.REDUCED_FAMILIES)]
                if text.name.startswith('fsv_unrolled_')
            for family in families for cache in ('plain', 'cached')
        } | {
            (text.stem, 'unified', 'unified', cache)
            for text in (repository / 'tools/gkr_verifier').glob('fsv_*.text')
                if not text.name.startswith('fsv_unrolled_')
            for cache in ('plain', 'cached')
        }
        self.assertEqual(committed, expected_committed)
        self.assertEqual(len(committed), 22)
        with tempfile.TemporaryDirectory() as directory:
            text = Path(directory) / 'multiblock_batch.text'
            text.write_bytes(struct.pack('<I', 0x13))
            text.with_suffix('.bin').write_bytes(text.read_bytes())
            production = run(['--program', str(text), '--configs', 'full,unified'])
            self.assertEqual(production, {
                ('multiblock_batch', config, family, cache)
                for config, families in [('full', decoder.POOLED_FAMILIES), ('unified', ('unified',))]
                for family in families for cache in ('plain', 'cached')
            })
            self.assertEqual(len(small) + len(committed) + len(production), 126)


class DecoderProcessTest(unittest.TestCase):
    def test_changed_oracle_value_fails_the_command(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            text = root / 'public.text'
            text.write_bytes(struct.pack('<I', 0x13))
            text.with_suffix('.bin').write_bytes(text.read_bytes())
            mask = [True] * 7 + [False, True]
            artifact = {
                'field_modulus': 2013265921, 'trace_len': 1,
                'program': {'text_words': 1},
                'circuit': {'decode_table_columns_mask': mask,
                            'tables_ids_in_generic_lookups': False,
                            'offset_for_decoder_table': 0, 'total_tables_size': 1},
                'columns': [{'blocks': [{'kind': 'dense', 'values': [value]}]}
                            for value in [0, 0, 0, 0, 0, 0, 0, 1]],
            }
            exporter = root / 'exporter'
            exporter.write_text('#!' + sys.executable + '\nimport pathlib, sys\n'
                                + 'pathlib.Path(sys.argv[4]).write_text(' + repr(json.dumps(artifact)) + ')\n')
            oracle = root / 'oracle'
            exporter.chmod(0o755)
            command = [sys.executable, str(Path(decoder.__file__)), '--exporter', str(exporter),
                       '--oracle', str(oracle), '--program', str(text), '--configs', 'full',
                       '--families', 'add-sub', '--cache-modes', 'plain']
            for value, code in [(0, 0), (4, 1)]:
                oracle.write_text('#!' + sys.executable + '\nimport pathlib, sys\n'
                                  + 'pathlib.Path(sys.argv[4]).write_text('
                                  + repr(f'0,{value},0,0,0,0,0,0,0,1,{value},0,0,0,0,0,0,1\n') + ')\n')
                oracle.chmod(0o755)
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, code, result.stderr)
                if code:
                    self.assertIn('decoder row 0, column 0', result.stderr)

    def test_omitted_nonzero_field_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            text = root / 'public.text'
            def run(command, label):
                if label.endswith('native export'):
                    Path(command[4]).write_text('{}')
                else:
                    Path(command[4]).write_text('0,0,0,0,0,0,0,0,1,1\n')
            with patch.object(decoder, 'run_checked', run):
                with self.assertRaisesRegex(ValueError, 'nonzero omitted field'):
                    decoder.run_case(Path('/exporter'), Path('/oracle'), root, text,
                                     text, 'full', 'add-sub', 'plain')


if __name__ == '__main__':
    unittest.main()
