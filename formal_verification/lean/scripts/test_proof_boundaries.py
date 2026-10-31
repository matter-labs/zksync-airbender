#!/usr/bin/env python3
"""Controls for the public compiler semantics dependency boundary."""
import unittest
from unittest.mock import patch

import check_proof_boundaries as boundaries


class CompilerSemanticBoundaryTests(unittest.TestCase):
    def test_indirect_calculation_is_rejected(self):
        root = 'Airbender.Review.Compiler.Operands'
        graph = {
            root: ['Airbender.Import.OperandData'],
            'Airbender.Import.OperandData': ['Airbender.Import.Intermediate'],
            'Airbender.Import.Intermediate': ['Airbender.Proofs.HiddenCalculation'],
        }
        with patch.object(boundaries, 'IMPORTS', graph):
            with self.assertRaisesRegex(ValueError, 'HiddenCalculation'):
                boundaries.check_compiler_semantics(root)

    def test_indirect_literal_data_is_allowed(self):
        root = 'Airbender.Review.Compiler.Operands'
        graph = {
            root: ['Airbender.Import.OperandData'],
            'Airbender.Import.OperandData': ['Airbender.Import.Schema'],
        }
        with patch.object(boundaries, 'IMPORTS', graph):
            boundaries.check_compiler_semantics(root)

    def test_current_public_semantics_are_independent(self):
        for module in ('Arithmetic', 'RowFrame', 'NativeRow', 'LookupArgument',
                       'LookupOperands', 'Setup'):
            boundaries.check_compiler_semantics('Airbender.Review.Compiler.' + module)

    def test_only_exact_legacy_reexports_are_allowed(self):
        for name in boundaries.COMPILER_BINDINGS:
            expected = name.replace('Airbender.Review.Compiler.',
                                    'Airbender.Proofs.Compatibility.Compiler.', 1)
            source = 'import ' + expected + '\n-- Legacy compatibility import.\n'
            self.assertTrue(boundaries.compatibility_reexport(name, source))
            for extra in ('def hidden := True', 'theorem hidden : True := by trivial',
                          'import Airbender.Proofs.HiddenCalculation'):
                self.assertFalse(boundaries.compatibility_reexport(name, source + extra))
            self.assertFalse(boundaries.compatibility_reexport(name + 'Other', source))

    def test_canonical_semantics_cannot_reach_a_legacy_reexport(self):
        root = 'Airbender.Review.Compiler.Operands'
        shim = 'Airbender.Review.Compiler.Pooled'
        graph = {root: [shim], shim: ['Airbender.Proofs.Compatibility.Compiler.Pooled']}
        with patch.object(boundaries, 'IMPORTS', graph):
            with self.assertRaisesRegex(ValueError, 'Compatibility'):
                boundaries.check_compiler_semantics(root)

    def test_program_bindings_keep_direct_import_and_statement_rules(self):
        for name in boundaries.PROGRAM_BINDINGS:
            source = boundaries.MODULES[name].read_text()
            self.assertFalse(any(dependency.startswith('Airbender.Proofs.')
                                 for dependency in boundaries.IMPORTS[name]))
            self.assertNotRegex(source, r'(?m)^\s*(?:theorem|lemma)\s')
            self.assertFalse(boundaries.compatibility_reexport(name, source))


if __name__ == '__main__':
    unittest.main()
