"""Require cached captures, all memory field groups and safe generation."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_memory_frame as generator
import gkr_memory_frame_instances as interface


class NumericMemoryFrameTests(unittest.TestCase):
    def test_complete_both_cache_modes(self):
        self.assertEqual(len(generator.CASES),11)
        self.assertEqual(set(generator.CASES),{'AddSubCached','WordMemoryCached','SubwordMemoryCached','BigintCached','BlakeGCached','BlakeRoundCached','KeccakCached'})
        for case in generator.CASES:
            generated=dict(generator.modules(case));stem='Airbender.Proofs.GKRProtocol.MemoryFrameChecks.'+case
            self.assertEqual(generated[stem+'.Certificate'].count(':= by decide +kernel'),1)
            if case in generator.SMALL_CASES:
                self.assertIn('check_sound_of_binding',generated[stem+'.Certificate'])
                self.assertIn('numeric_data_binding source_binding : data =',generated[stem+'.Bindings'])
            else:
                from gkr_packed_memory_frame_bounded import capture_shape
                inputs,arity,size=capture_shape(case)
                if case.startswith('BlakeRound'):self.assertEqual((inputs,arity,size),(763,771,616))
                self.assertLessEqual(inputs,arity)
                self.assertEqual(len(generated),9)
                self.assertIn('check_sound data',generated[stem+'.Certificate'])
                self.assertNotIn('source_binding',generated[stem+'.Bindings'])
                self.assertIn('ofTypedPrefix_eq',generated[stem+'.Bindings'])
                for name in ['placement','nativeAddress','inputAddress','fullAddress']:
                    text=generated[stem+'.'+name[0].upper()+name[1:]+'Bindings']
                    for first in range(0,arity,32):self.assertIn(f'{name}Leaf{first} :',text)
                    self.assertIn(f'complete_binding data.{name}.toList (List.ofFn {name}Source) {arity}',text)
                for first in range(0,size,16):self.assertIn(f'ramLeaf{first} :',generated[stem+'.FieldsBindings'])
                self.assertIn(f'ramFields.length = {size}',generated[stem+'.FieldsBindings'])
            for field in ['ramFields','initializationFields','executeFields','activeCoordinates','allCoordinates','sourcePlacement','inputBank','bank']:
                self.assertIn('.'+field,generator.source(case))
            from gkr_packed_query_frame import capture_name
            _,source=interface.module(capture_name(case),case)
            self.assertIn('using_check Airbender.Compiler.MemoryFrameChecks.'+case+'.originalChecked',source)
            self.assertNotIn('maxHeartbeats',source)
            for phase in [1,2]:
                with self.assertRaisesRegex(ValueError,'do not use proof shards'):
                    interface.module('add-sub-cached',case,phase=phase)

    def test_changed_input_prefix_stops_generation(self):
        import gkr_packed_memory_frame_bounded as bounded
        with patch.object(bounded,'synthesize',return_value={'inputs':['changed address']}):
            with self.assertRaisesRegex(ValueError,'memory input prefix changed'):
                list(generator.modules('BlakeRoundCached'))

    def test_legacy_interface_stays_available(self):
        with patch.object(generator,'CASES',()):
            _,source=interface.module('jump-branch-cached','JumpBranchCached')
        self.assertNotIn('using_check',source)
        self.assertIn('set_option maxHeartbeats 4000000',source)

    def test_untracked_sources_stop_before_writes(self):
        for inputs in [False,True]:
            with tempfile.TemporaryDirectory() as directory:
                root=Path(directory);relative='Airbender/Proofs/GKRProtocol/'+('MemoryFrameNative/AddSubCachedInputs.lean' if inputs else 'MemoryFrameChecks/AddSubCached/Data.lean')
                path=root/relative;path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
                with patch('gkr_packed_rotate_boundary.LEAN',root),contextlib.redirect_stdout(io.StringIO()):
                    if inputs:
                        from gkr_packed_rotate_boundary import preflight
                        with self.assertRaisesRegex(ValueError,'untracked capture source'):
                            preflight([interface.module('add-sub-cached','AddSubCached',phase=0)])
                    else:
                        with patch('sys.argv',['gkr_packed_memory_frame.py','--case','AddSubCached','--write']):
                            with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
                self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
