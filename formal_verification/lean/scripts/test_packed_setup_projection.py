"""Keep the packed setup capture and its public projections in the same scope."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_unified_equal_chunks as generator


class PackedSetupProjectionTests(unittest.TestCase):
    def test_one_module_preserves_the_public_fact_names(self):
        modules = list(generator.modules(2))
        self.assertEqual(len(modules), 1)
        name, source = modules[0]
        self.assertEqual(name, 'Airbender.Proofs.GKRProtocol.UnifiedEqualParts.Column2.Projected')
        self.assertNotIn('column_blocks_part', source)
        self.assertNotIn('maxHeartbeats', source)
        for index in range(1, 22):
            self.assertIn(f'theorem chunkSame{index} : original{index} = target{index}', source)
            self.assertIn(f'theorem chunkLength{index} : (original{index}.map Setup.Block.length).sum', source)

    def test_wide_capture_keeps_the_gap_and_all_public_facts(self):
        modules = list(generator.modules(5))
        self.assertEqual(len(modules), 1)
        name, source = modules[0]
        self.assertEqual(name, 'Airbender.Proofs.GKRProtocol.UnifiedEqualParts.Column5.Projected')
        self.assertEqual(source.count('theorem chunkSame'), 204)
        self.assertEqual(source.count('theorem chunkLength'), 204)
        self.assertNotIn('original191 :', source)
        self.assertIn('original192 : List Setup.Block :=\n  UnifiedPackedEquality.Column5.sourceChunk 24320', source)
        self.assertNotIn('column_blocks_part', source)
        self.assertNotIn('maxHeartbeats', source)

    def test_scope_drift_stops_before_it_changes_files(self):
        relative = Path('Airbender/Proofs/GKRProtocol/UnifiedPackedEqualityCodes.lean')
        source = (generator.LEAN / relative).read_text()
        changed = source.replace('⟨0, 128, 2360⟩', '⟨0, 128, 2361⟩', 1)
        self.assertNotEqual(source, changed)
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            capture = scratch / relative
            capture.parent.mkdir(parents=True)
            capture.write_text(changed)
            legacy = scratch / 'Airbender/Proofs/GKRProtocol/UnifiedEqualParts/Column2/Part0.lean'
            legacy.parent.mkdir(parents=True)
            legacy.write_text('retained source\n')
            with patch.object(generator, 'LEAN', scratch), patch(
                    'sys.argv', ['gkr_unified_equal_chunks.py', '--column', '2', '--write']), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError, 'capture scope or row-count statements'):
                    generator.main()
            self.assertEqual(legacy.read_text(), 'retained source\n')
            self.assertFalse((legacy.parent / 'Projected.lean').exists())

    def test_write_preserves_an_untracked_file_at_a_retired_path(self):
        relative = Path('Airbender/Proofs/GKRProtocol/UnifiedPackedEqualityCodes.lean')
        source = (generator.LEAN / relative).read_text()
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            capture = scratch / relative
            capture.parent.mkdir(parents=True)
            capture.write_text(source)
            legacy = scratch / 'Airbender/Proofs/GKRProtocol/UnifiedEqualParts/Column2/Part0.lean'
            legacy.parent.mkdir(parents=True)
            legacy.write_text('unrelated untracked source\n')
            with patch.object(generator, 'LEAN', scratch), patch(
                    'sys.argv', ['gkr_unified_equal_chunks.py', '--column', '2', '--write']), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError, 'untracked legacy shard'):
                    generator.main()
            self.assertEqual(legacy.read_text(), 'unrelated untracked source\n')
            self.assertFalse((legacy.parent / 'Projected.lean').exists())


if __name__ == '__main__':
    unittest.main()
