"""Keep the native rotation boundary and its complete checker in scope."""
import contextlib
import copy
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_rotate_boundary as generator


class RotationBoundaryTests(unittest.TestCase):
    def test_complete_native_scope_and_original_names(self):
        modules=dict(generator.modules())
        self.assertEqual(len(modules),5)
        self.assertEqual(modules[generator.STEM+'.Certificate'].count('theorem checked'),1)
        data=modules[generator.STEM+'.Data']
        self.assertNotIn('theorem follows14',data)
        self.assertNotIn('maxHeartbeats',data)
        self.assertEqual(data.count('column_blocks_part part14_'),12)
        wrapper=modules['Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit14']
        self.assertIn('theorem follows14',wrapper)
        self.assertIn('theorem length14',wrapper)
        self.assertNotIn('maxHeartbeats',wrapper)

    def test_program_region_scope_drift_stops_before_writes(self):
        plan=copy.deepcopy(generator.plans(1))
        plan[0]['tables'][plan[4][14][0]['region']]['id']=34
        with patch.object(generator,'plans',return_value=plan):
            with self.assertRaisesRegex(ValueError,'scope changed'):
                list(generator.modules())

    def test_write_preserves_untracked_capture_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            source=root/(generator.STEM.replace('.','/')+'/Data.lean')
            source.parent.mkdir(parents=True)
            source.write_text('unrelated untracked source\n')
            with patch.object(generator,'LEAN',root),patch('sys.argv',['gkr_packed_rotate_boundary.py','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):
                    generator.main()
            self.assertEqual(source.read_text(),'unrelated untracked source\n')
            self.assertFalse(source.with_name('Certificate.lean').exists())


if __name__=='__main__':unittest.main()
