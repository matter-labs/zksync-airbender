"""Require complete functional ports, both modes and exact source freshness."""
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_functional_steps as generator
import gkr_functional_instances as interface


class FunctionalStepTests(unittest.TestCase):
    def test_complete_modes_and_old_step_names(self):
        self.assertEqual(len(generator.CASES), 22)
        self.assertEqual(set(generator.CASES), {stem + mode for stem in generator.CIRCUIT_CASES
                                              for mode in ['Cached', 'Uncached']})
        self.assertEqual([len(generator.capture(case)) for case in generator.DENSE_CASES], [674, 394])
        for case in generator.CASES:
            count = len(generator.capture(case))
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.FunctionalStepChecks.' + case
            self.assertEqual(len(generated), 4)
            certificate = generated[stem + '.Certificate']
            self.assertEqual(certificate.count(':= by decide +kernel'), 1)
            self.assertIn('tree_check_sound', certificate)
            bindings = generated[stem + '.Bindings']
            for first in range(0, count, 8):
                self.assertIn(f'portsPiece{first} :', bindings)
            self.assertIn(f'complete_binding ports sourcePorts {count}', bindings)
            corollaries = generated[stem + '.Corollaries']
            self.assertEqual(corollaries.count('theorem stepChecked'), count)
            for index in range(count):
                self.assertIn(f'theorem stepChecked{index} : step{index}.check isBase known{index} = true', corollaries)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))
            name = generator.capture_name(case)
            pair = json.loads((generator.LEAN / f'artifacts/compiler/{name}.json').read_text())
            targets, _, _ = interface.modules(name, case, pair)
            self.assertFalse(any('Steps' in module for module, _ in targets))
            self.assertIn(stem + '.Corollaries', targets[-1][1])
            self.assertTrue(any('Base0' in module for module, _ in targets))
            self.assertIn('noncomputable def native.canonical', targets[0][1])
            self.assertNotIn('FunctionalStepChecks', targets[0][1])

    def test_stale_hash_is_rejected(self):
        with patch.object(generator, 'digest', return_value='changed'):
            with self.assertRaisesRegex(ValueError, 'source hashes changed'):
                generator.capture('BlakeRoundCached')

    def test_invalid_or_incomplete_payload_is_rejected(self):
        case = 'BlakeRoundCached'
        payload = json.loads((generator.DATA / (generator.capture_name(case) + '.json')).read_text())
        mutations = []
        changed = copy.deepcopy(payload); changed['ports'].pop(); mutations.append(changed)
        changed = copy.deepcopy(payload); changed['ports'][0]['outputs'][0][1] = 2; mutations.append(changed)
        changed = copy.deepcopy(payload); changed['ports'][0]['inputs'][0][0] = True; mutations.append(changed)
        for changed in mutations:
            with patch.object(generator.json, 'loads', side_effect=[changed, json.loads((generator.LEAN / generator.source_paths(case)[0]).read_text())]):
                with self.assertRaises(ValueError):
                    generator.capture(case)

    def test_legacy_steps_remain_available(self):
        case, name = 'AddSubCached', 'add-sub-cached'
        pair = json.loads((generator.LEAN / f'artifacts/compiler/{name}.json').read_text())
        with patch.object(generator, 'CASES', ()):
            targets, _, _ = interface.modules(name, case, pair)
        self.assertTrue(any(module.endswith('Steps0') for module, _ in targets))
        self.assertIn('check_functional_graph native phase 0', dict(targets)[targets[1][0]])

    def test_untracked_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/FunctionalStepChecks/BlakeRoundCached/Data.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_functional_steps.py', '--case', 'BlakeRoundCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):
                        generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':
    unittest.main()
