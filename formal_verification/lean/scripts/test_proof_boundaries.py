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


if __name__ == '__main__':
    unittest.main()
