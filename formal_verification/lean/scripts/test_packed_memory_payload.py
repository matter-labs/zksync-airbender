"""Check original memory predicate coverage and cached captures."""
import unittest
import gkr_packed_memory_payload as packed
import gkr_memory_certificate as legacy


class MemoryPayload(unittest.TestCase):
    def test_complete_original_predicates(self):
        for case in packed.CASES:
            selected = list(packed.entries(case))
            cert = packed.selectors(case)
            expected = 1 + 2 * len(cert['leaves']) + sum(
                len(group['native_leaves']) + int(group['mask'] is not None)
                for group in cert['groups'].values())
            self.assertEqual(len(selected), expected)
            modules = dict(packed.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case
            self.assertEqual(modules[stem + '.Certificate'].count('by decide +kernel'), 1)
            self.assertEqual(modules[stem + '.Certificate'].count('NumericNativePayloadChecks.checked_at'), expected)
            self.assertIn('projection_source_binding', modules[stem + '.Bindings'])
            self.assertNotIn('witness := []', '\n'.join(modules.values()))

    def test_original_data_and_cache_modes(self):
        for case in packed.CASES:
            self.assertTrue(case.endswith('Cached') and not case.endswith('Uncached'))
            text = packed.inputs(case)
            self.assertIn('phase 0', text)
            self.assertNotIn('NumericMemoryPayloadChecks', text)
            self.assertNotIn('maxHeartbeats', packed.native(case)[1])
            self.assertEqual(list(legacy.modules(packed.capture_name(case), case)),
                [('Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case + '.Inputs', text), packed.native(case)])


if __name__ == '__main__':
    unittest.main()
