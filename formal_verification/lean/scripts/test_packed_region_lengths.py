"""Keep every fixed region-part length and exclude program ROM."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_region_lengths as generator
from gkr_unified_prefix import plans
from gkr_unified_prefix_assembly import column_module


class FixedRegionLengthTests(unittest.TestCase):
    def test_complete_fixed_scope_and_one_closed_result(self):
        expected={2:159,3:17,4:564,5:595,6:425,7:427}
        self.assertEqual(set(generator.COLUMNS),set(expected))
        for column,count in expected.items():
            entries=generator.metadata_plan(column);artifact=plans(column)[0]
            self.assertEqual(len(entries),count)
            for entry in entries:self.assertNotEqual(artifact['tables'][entry['region']]['id'],34)
            modules=dict(generator.modules(column));stem=f'Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column{column}'
            self.assertEqual(modules[stem+'.Certificate'].count('theorem checked :'),1)
            self.assertEqual(modules[stem+'.Data'].count('noncomputable def view'),count)
            self.assertEqual(modules[stem].count('theorem length'),count)
            consumer=column_module(column)[1]
            self.assertEqual(consumer.count(f'Airbender.Compiler.UnifiedRegionLengths.Column{column}.length'),count)
            self.assertNotIn('PackedSetupNormalization',modules[stem+'.Certificate'])

    def test_known_views_reuse_complete_bindings(self):
        source=dict(generator.modules(3))['Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column3.Bindings']
        self.assertEqual(source.count('congrArg (fun blocks'),7)
        self.assertEqual(source.count('numeric_data_binding binding'),10)

    def test_untracked_data_stops_before_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'Airbender/Proofs/GKRProtocol/UnifiedRegionLengths/Column3/Data.lean'
            path.parent.mkdir(parents=True);path.write_text('unrelated untracked source\n')
            with patch('gkr_packed_rotate_boundary.LEAN',root),patch('sys.argv',['gkr_packed_region_lengths.py','--column','3','--write']),contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(),'unrelated untracked source\n')


if __name__=='__main__':unittest.main()
