"""Retain complete base ports, original residuals and cached captures."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import gkr_packed_functional_base as generator
import gkr_functional_instances as interface
from gkr_packed_query_frame import capture_name


class FunctionalBaseTests(unittest.TestCase):
    def test_complete_native_references(self):
        self.assertEqual(set(generator.CASES), {stem + mode for stem in generator.CIRCUIT_CASES
                                              for mode in ['Cached']})
        for case in generator.CASES:
            generated = dict(generator.modules(case))
            stem = 'Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.' + case
            self.assertEqual(len(generated), 4)
            bindings = generator.base_bindings(case)
            typed = generated[stem + '.Typed']
            for index, binding in enumerate(bindings):
                self.assertIn(f'.baseRecipe{index}', typed)
                self.assertIn(f'.baseOutput{index}', typed)
                self.assertIn(f'.gate{binding["gate"]}.inputResidual', typed)
            self.assertIn('.bank', typed)
            self.assertIn('.isBase', typed)
            self.assertIn('source_binding', generated[stem + '.Bindings'])
            if case == 'BlakeRoundCached':
                self.assertEqual(len(bindings), 95)
                for index in range(95):
                    self.assertIn(f'piece{index} :', generated[stem + '.Bindings'])
            self.assertIn('check_sound originalEntries data source_binding checked', generated[stem + '.Certificate'])
            certificate = generated[stem + '.Certificate']
            for index in range(len(bindings)):
                self.assertIn(f'theorem baseFacts{index} :', certificate)
            self.assertNotIn(stem + '.Corollaries', generated)
            self.assertNotIn('maxHeartbeats', ''.join(generated.values()))
            name = capture_name(case)
            pair = json.loads((generator.LEAN / f'artifacts/compiler/{name}.json').read_text())
            targets, _, _ = interface.modules(name, case, pair)
            self.assertFalse(any('Base0' in module for module, _ in targets))
            self.assertIn(stem + '.Certificate', targets[-1][1])
            self.assertIn(f'using_base Airbender.Compiler.FunctionalBaseChecks.{case}', targets[-1][1])

    def test_legacy_base_checks_stay_available(self):
        name, case = 'mul-div-cached', 'MulDivCached'
        pair = json.loads((generator.LEAN / f'artifacts/compiler/{name}.json').read_text())
        with patch.object(generator, 'CASES', ()):
            targets, _, _ = interface.modules(name, case, pair)
        self.assertTrue(any(module.endswith('Base0') for module, _ in targets))

    def test_untracked_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Airbender/Proofs/GKRProtocol/FunctionalBaseChecks/AddSubCached/Data.lean'
            path.parent.mkdir(parents=True)
            path.write_text('unrelated source\n')
            with patch('gkr_packed_rotate_boundary.LEAN', root), contextlib.redirect_stdout(io.StringIO()):
                with patch('sys.argv', ['gkr_packed_functional_base.py', '--case', 'AddSubCached', '--write']):
                    with self.assertRaisesRegex(ValueError, 'untracked capture source'):
                        generator.main()
            self.assertEqual(path.read_text(), 'unrelated source\n')


if __name__ == '__main__':
    unittest.main()
