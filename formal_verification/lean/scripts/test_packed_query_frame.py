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
        self.assertEqual(len(generator.CASES),22)
        self.assertEqual(len(set(generator.CASES)),22)
        for stem in generator.CIRCUIT_CASES:
            self.assertIn(stem+'Cached',generator.CASES)
            self.assertIn(stem+'Uncached',generator.CASES)
        for case in generator.CASES:
            modules=dict(generator.modules(case));stem='Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+case
            self.assertEqual(modules[stem+'.Certificate'].count(':= by decide +kernel'),1)
            if case in generator.LARGE_CASES:
                self.assertIn('indexedCheck views data.fields',modules[stem+'.Certificate'])
                self.assertIn('check_sound data',modules[stem+'.Certificate'])
                self.assertIn('coordinates_binding',modules[stem+'.Bindings'])
            else:
                self.assertIn('numeric_data_binding source_binding : data =',modules[stem+'.Bindings'])
            for field in ['fields','coordinates','originalProjection','sourcePlacement','inputBank','bank']:
                self.assertIn('.'+field,generator.source(case))
            _,source=interface.module(generator.capture_name(case),case)
            self.assertIn('using_check Airbender.Compiler.QueryFrameChecks.'+case+'.originalChecked',source)
            self.assertNotIn('maxHeartbeats',source)

    def test_large_bindings_cover_complete_sources(self):
        import re
        for case in generator.LARGE_CASES:
            arity,size=generator.capture_shape(case)
            generated=dict(generator.modules(case));stem='Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+case
            for role,field,width,total in [('Placement','placement',32,arity),('NativeAddress','nativeAddress',32,arity),
                    ('ReturnedAddress','returnedAddress',32,arity),('Fields','fields',16,size)]:
                source=generated[stem+'.'+role+'Bindings']
                starts=[int(value) for value in re.findall(r'numeric_data_binding '+field+r'Leaf(\d+)',source)]
                self.assertEqual(starts,list(range(0,total,width)))
                self.assertIn('complete_binding',source)
            _,source=interface.module(generator.capture_name(case),case)
            self.assertIn('using_check',source)
            self.assertIn('phase 3 start 0 stop '+str(size),source)
            self.assertNotIn('maxHeartbeats',source)
            self.assertNotIn('Part',source)
            for phase in [1,2]:
                with self.assertRaisesRegex(ValueError,'do not use proof shards'):
                    interface.module(generator.capture_name(case),case,phase=phase)

    def test_materializer_budgets_are_scoped(self):
        for case in generator.CASES:
            source=dict(generator.modules(case))['Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+case+'.Data']
            if case in generator.MATERIALIZATION_BUDGET_CASES:
                self.assertIn('set_option maxHeartbeats 2000000 in\nnumeric_query_frame_capture',source)
            else:
                self.assertNotIn('maxHeartbeats',source)
            _,wrapper=interface.module(generator.capture_name(case),case)
            self.assertNotIn('Part',wrapper)

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
