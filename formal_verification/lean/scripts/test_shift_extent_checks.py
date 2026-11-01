"""Keep native partition geometry and old extent contracts intact."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import generate_shift_extent_checks as generator


class ShiftExtentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.artifact=json.loads((generator.ROOT/'artifacts/setup/shift-binop.json').read_text())

    def test_complete_capture_and_public_corollaries(self):
        for lane in range(4):
            capture,wrapper=list(generator.generated(self.artifact,lane))
            self.assertEqual(capture[1].count('theorem checked'),1)
            self.assertEqual(capture[1].count('theorem binding'),16)
            self.assertEqual(wrapper[1].count(f'theorem output{lane}_extent'),16)
            self.assertNotIn('dsimp',wrapper[1])
            self.assertNotIn('maxSteps',wrapper[1])

    def test_contract_change_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);artifact=root/'artifacts/setup/shift-binop.json';artifact.parent.mkdir(parents=True)
            artifact.write_text(json.dumps(self.artifact))
            path=root/'Airbender/Proofs/Tables/ShiftOutputExtent0.lean';path.parent.mkdir(parents=True)
            source=list(generator.generated(self.artifact,0))[-1][1].replace('sum = 26881','sum = 26882',1)
            path.write_text(source)
            with patch.object(generator,'ROOT',root),patch('sys.argv',['generate_shift_extent_checks.py','--lane','0','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'statements changed'):generator.main()
            self.assertEqual(path.read_text(),source)
            self.assertFalse(path.with_name('ShiftExtentChecks0.lean').exists())

    def test_untracked_capture_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);artifact=root/'artifacts/setup/shift-binop.json';artifact.parent.mkdir(parents=True)
            artifact.write_text(json.dumps(self.artifact))
            path=root/'Airbender/Proofs/Tables/ShiftExtentChecks0.lean';path.parent.mkdir(parents=True)
            path.write_text('unrelated untracked source\n')
            with patch.object(generator,'ROOT',root),patch('sys.argv',['generate_shift_extent_checks.py','--lane','0','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked extent source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
