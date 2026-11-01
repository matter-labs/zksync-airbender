"""Check complete fixed scope and retained program proofs."""
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_column1_spans as generator
import gkr_unified_prefix as legacy


class FixedColumnOneTests(unittest.TestCase):
    def test_complete_scope_and_original_names(self):
        _,_,chosen=generator.capture_plan()
        self.assertEqual(chosen,list(range(12))+list(range(15,33)))
        modules=dict(generator.modules())
        self.assertEqual(len(modules),5)
        self.assertEqual(modules[generator.STEM+'.Data'].count('noncomputable def source'),30)
        self.assertEqual(modules[generator.STEM+'.Projected'].count('theorem follows'),30)
        self.assertEqual(modules[generator.STEM+'.Projected'].count('theorem length'),30)
        self.assertEqual(modules[generator.STEM+'.Certificate'].count('by decide +kernel'),1)
        assembly=legacy.pilot_assembly()[1]
        for index in [12,13,14,33]:self.assertIn(f'.Unit{index}\n',assembly)
        self.assertNotIn('.Unit15\n',assembly)

    def test_scope_drift_stops(self):
        plan=copy.deepcopy(generator.plans(1))
        plan[0]['tables'][plan[4][0][0]['region']]['id']=34
        with patch.object(generator,'plans',return_value=plan):
            with self.assertRaisesRegex(ValueError,'scope changed'):list(generator.modules())

    def test_untracked_retired_source_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/(generator.PARTS.replace('.','/')+'/Unit15.lean')
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch.object(generator,'LEAN',root):
                with self.assertRaisesRegex(ValueError,'untracked column-one source'):generator.prepare([],write=True)
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
