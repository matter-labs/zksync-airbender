"""Keep complete prefix checks, source bindings and old interfaces together."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_shift_prefix as packed
import gkr_shift_prefix_instances as legacy


class CompleteShiftPrefixTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.artifact = json.loads((packed.LEAN / 'artifacts/setup/shift-binop.json').read_text())

    def test_all_columns_have_one_complete_result(self):
        for column in packed.ADOPTED:
            modules = dict(packed.capture(self.artifact, column))
            self.assertEqual(len(modules), 5)
            certificate = next(source for name, source in modules.items() if name.endswith('.Certificate'))
            self.assertEqual(certificate.count('by decide +kernel'), 1)
            self.assertIn('check_sound_at requests checked index', certificate)
            data = next(source for name, source in modules.items() if name.endswith('.Data'))
            self.assertNotIn('theorem chunk', data)
            projected = next(source for name, source in modules.items() if name.endswith('.Projected'))
            self.assertNotIn('column_blocks_part', projected)
            self.assertNotIn('normalizeSetupBlocks original0 = normalizeSetupBlocks target0 := by rfl', projected)

    def test_native_packing_scope_stays_exact(self):
        for column in [0, 2, 7]:
            modules = dict(packed.capture(self.artifact, column))
            codes = next(source for name, source in modules.items() if name.endswith('.Codes'))
            self.assertEqual('packed_region 7' in codes, column == 2)
            packed_regions = [line for line in codes.splitlines() if 'packed_bytes 1' in line]
            self.assertTrue(all('region 7 column 2 ' in line for line in packed_regions))

    def test_write_preserves_untracked_retired_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            artifact = root / 'artifacts/setup/shift-binop.json'
            artifact.parent.mkdir(parents=True)
            artifact.write_text(json.dumps(self.artifact))
            old = root / 'Airbender/Proofs/GKRProtocol/ShiftPrefixParts/Column0/Part0.lean'
            old.parent.mkdir(parents=True)
            old.write_text('unrelated untracked source\n')
            with patch.object(legacy, 'LEAN', root), patch('sys.argv', ['gkr_shift_prefix_instances.py', '--column', '0', '--write']), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError, 'untracked legacy shard'):
                    legacy.main()
            self.assertEqual(old.read_text(), 'unrelated untracked source\n')
            self.assertFalse((root / 'Airbender/Proofs/GKRProtocol/ShiftPrefixChecks').exists())


if __name__ == '__main__':
    unittest.main()
