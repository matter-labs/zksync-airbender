"""Keep fixed special spans complete and program spans outside their scope."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_special_spans as packed
import gkr_unified_special_chunks as legacy


class FixedSpecialSpanTests(unittest.TestCase):
    def test_scope_and_one_closed_result_per_column(self):
        expected={2:126,3:1,4:352,5:376,6:221,7:220}
        for column,count in expected.items():
            artifact,groups,_,chosen,excluded=packed.capture_plan(column)
            self.assertEqual(len(chosen),count)
            self.assertTrue(excluded)
            for index in chosen:
                self.assertTrue(all(entry['region'] is not None and artifact['tables'][entry['region']]['id']!=34 for entry in groups[index]))
            modules=dict(packed.modules(column))
            certificate=modules[f'Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column{column}.Certificate']
            self.assertEqual(certificate.count('theorem checked'),1)
            projected=modules[f'Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column{column}.Projected']
            self.assertEqual(projected.count('theorem follows'),count)
            self.assertEqual(projected.count('theorem length'),count)
            self.assertNotIn('maxHeartbeats',projected)

    def test_program_proofs_keep_their_own_source(self):
        generated=dict(packed.modules(3,include_legacy=True))
        retained=generated['Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column3.Chunk0.Part0']
        self.assertIn('theorem follows1',retained)
        self.assertIn('theorem follows2',retained)
        self.assertNotIn('theorem follows0',retained)
        self.assertNotIn('noncomputable def source',retained)
        data=generated['Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Data']
        self.assertEqual(data.count('noncomputable def source'),3)

    def test_untracked_retired_source_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            path=root/'Airbender/Proofs/GKRProtocol/UnifiedSpecialParts/Column3/Chunk0/Part9.lean'
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch.object(legacy,'LEAN',root),patch('sys.argv',['gkr_unified_special_chunks.py','--column','3','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked special-span source'):legacy.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')
            self.assertFalse((root/'Airbender/Proofs/GKRProtocol/UnifiedFixedSpans').exists())


if __name__=='__main__':unittest.main()
