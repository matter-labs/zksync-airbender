"""Keep complete query fields, both cache modes and exact numeric bindings."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_query_frame as generator
import gkr_query_frame_instances as interface


class NumericQueryFrameTests(unittest.TestCase):
    def test_complete_both_cache_modes(self):
        self.assertEqual(generator.CASES,('AddSubCached','AddSubUncached'))
        for case in generator.CASES:
            modules=dict(generator.modules(case));stem='Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+case
            self.assertEqual(modules[stem+'.Certificate'].count(':= by decide +kernel'),1)
            self.assertIn('numeric_data_binding source_binding : data =',modules[stem+'.Bindings'])
            for field in ['fields','coordinates','originalProjection','sourcePlacement','inputBank','bank']:
                self.assertIn('.'+field,generator.source(case))
            _,source=interface.module('add-sub-'+('cached' if case.endswith('Cached') else 'uncached'),case)
            self.assertIn('using_check Airbender.Compiler.QueryFrameChecks.'+case+'.originalChecked',source)
            self.assertNotIn('maxHeartbeats',source)

    def test_unadopted_interface_stays_the_same(self):
        name,source=interface.module('jump-branch-cached','JumpBranchCached')
        self.assertNotIn('using_check',source)
        self.assertEqual((interface.LEAN/(name.replace('.','/')+'.lean')).read_text(),source)

    def test_untracked_capture_and_inputs_stop_before_writes(self):
        for inputs in [False,True]:
            with tempfile.TemporaryDirectory() as directory:
                root=Path(directory)
                relative='Airbender/Proofs/GKRProtocol/'+('QueryFrameNative/AddSubCachedInputs.lean' if inputs else 'QueryFrameChecks/AddSubCached/Data.lean')
                path=root/relative;path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
                with patch('gkr_packed_rotate_boundary.LEAN',root),contextlib.redirect_stdout(io.StringIO()):
                    if inputs:
                        generated=[interface.module('add-sub-cached','AddSubCached',phase=0)]
                        from gkr_packed_rotate_boundary import preflight
                        with self.assertRaisesRegex(ValueError,'untracked capture source'):preflight(generated)
                    else:
                        with patch('sys.argv',['gkr_packed_query_frame.py','--case','AddSubCached','--write']):
                            with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
                self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
