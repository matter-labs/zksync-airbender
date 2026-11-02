"""Keep complete source vectors, exact targets and cached captures."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import gkr_packed_source_freshness as generator


class FreshnessTests(unittest.TestCase):
    def test_complete_source_and_targets(self):
        self.assertEqual(len(generator.CASES), 11)
        self.assertEqual(sum(case.endswith('Uncached') for case in generator.CASES), 0)
        for case in generator.CASES:
            count, targets = generator.metadata(case)
            if case.startswith('BlakeRound'):
                self.assertEqual(count, 632)
                self.assertEqual([name for name, _ in targets], ['generic', 'timestamp'])
            self.assertTrue(count > 0 and targets)
            self.assertEqual(len({name for name, _ in targets}), len(targets))
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.' + case
            self.assertEqual(len(generated), 4)
            typed = generated[stem + '.Typed']
            self.assertIn('LookupSourceNative.' + case + '.native.bank.address', typed)
            self.assertIn('LookupNative.' + case + '.native.sourcePlacement index', typed)
            self.assertIn(f'(List.range {count}).map', typed)
            data = generated[stem + '.Data']
            self.assertEqual(data.count('numeric_functional_base_capture data'), (count + 7) // 8)
            self.assertIn(f'native.sourcePlacement {count - 1}', data)
            bindings = generated[stem + '.Bindings']
            self.assertIn(f'encode) {count}\n', bindings)
            self.assertIn('target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses', bindings)
            certificate = generated[stem + '.Certificate']
            self.assertEqual(certificate.count('theorem checked :'), 1)
            self.assertIn('check_sound sourceAddresses targetAddresses data targetData source_binding target_binding checked', certificate)
            for name, _ in targets:self.assertIn('theorem ' + name + 'Fresh :', certificate)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))

    def test_exact_original_predicate_and_legacy_branch(self):
        source = (generator.LEAN / 'Airbender/Import/GKRProtocol/TableImport.lean').read_text()
        self.assertIn('| none => `(by decide +kernel)', source)
        self.assertIn('!addressEqual (($bankName).address ($placementName index))', source)
        wrapper = generator.table_wrapper('BlakeRoundCached',
            'import Airbender.Proofs.GKRProtocol.LookupSourceNative.BlakeRoundCached\n'
            'set_option maxHeartbeats 4000000\n'
            '  roles Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing\n')
        self.assertIn('SourceFreshnessChecks.BlakeRoundCached.Certificate', wrapper)
        self.assertIn('using_freshness Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached', wrapper)
        self.assertNotIn('maxHeartbeats', wrapper)

    def test_untracked_capture_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/SourceFreshnessChecks/BlakeRoundCached/Typed.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_source_freshness.py', '--case', 'BlakeRoundCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':unittest.main()
