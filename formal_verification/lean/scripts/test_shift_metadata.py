"""Keep complete coverage and all original public contracts."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import generate_shift_metadata as generator


class ShiftMetadataTests(unittest.TestCase):
    def test_complete_metadata_and_one_closed_result(self):
        modules=dict(generator.modules())
        self.assertEqual(modules[generator.STEM+'.Certificate'].count(':= by decide +kernel'),1)
        public=modules['Airbender.Proofs.Tables.ShiftColumnCoverage']
        self.assertEqual(public.count('.regionLength'),40)
        self.assertEqual(public.count('.shiftLength'),10)
        for lane in range(10):
            for region in range(2,6):self.assertIn(f'ShiftPrefixNative.Column{lane}.regionLength{region}',public)
            self.assertIn(f'ShiftMetadata.shiftLength{lane}',public)
        for statement in [generator.SHIFT,generator.BINARY,generator.NATIVE]:self.assertIn(statement,public)
        self.assertNotIn('fin_cases',public)
        self.assertNotIn('decide +kernel\n',public)
        binary=modules['Airbender.Proofs.Tables.ImportedBinaryRows']
        start=binary.index('theorem coverage');end=binary.index('private theorem output_get',start)
        coverage=binary[start:end]
        self.assertIn(generator.OUTPUT_COVERAGE,coverage)
        for region in range(2,5):self.assertIn(f'ShiftPrefixNative.Column2.regionLength{region}',coverage)
        self.assertNotIn('simp only',coverage)
        self.assertNotIn('fin_cases',coverage)

    def test_contract_drift_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);source=root/'Airbender/Proofs/Tables/ShiftColumnCoverage.lean'
            source.parent.mkdir(parents=True)
            source.write_text((generator.LEAN/source.relative_to(root)).read_text().replace('sum = 262144','sum = 262143'))
            artifact=root/'artifacts/setup/shift-binop.json';artifact.parent.mkdir(parents=True)
            artifact.write_bytes((generator.LEAN/'artifacts/setup/shift-binop.json').read_bytes())
            with patch.object(generator,'LEAN',root):
                with self.assertRaisesRegex(ValueError,'contracts changed'):list(generator.modules())

    def test_untracked_source_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/(generator.STEM.replace('.','/')+'/Certificate.lean')
            path.parent.mkdir(parents=True);path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['generate_shift_metadata.py','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated source\n')


if __name__=='__main__':unittest.main()
