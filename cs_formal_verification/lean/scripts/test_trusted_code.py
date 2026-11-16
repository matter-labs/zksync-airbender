"""Regressions for reviewed module permissions and source checks."""
import unittest
from check_import_closure import check_graph
from check_trusted_code import check_source, manifest_list


class TrustedCodeTests(unittest.TestCase):
    def test_unlisted_procedures_and_attributes_fail(self):
        for code in ['unsafe def f := 0', 'partial def f := f',
                     '@[implemented_by f] def g := 0', '@[extern "foreign"] def f := 0']:
            with self.subTest(code=code), self.assertRaisesRegex(ValueError, 'unlisted'):
                check_source('Human.Example', code, {'Proven.Allowed'})

    def test_allowed_procedure_module_passes(self):
        self.assertTrue(check_source('Proven.Allowed', 'private partial def f := f', {'Proven.Allowed'}))

    def test_forbidden_features_fail_in_allowed_modules(self):
        for code in ['axiom bad : False', 'example : False := by sorry',
                     'example : True := by native_decide', 'example : True := by bv_decide']:
            with self.subTest(code=code), self.assertRaisesRegex(ValueError, 'prohibited'):
                check_source('Proven.Allowed', code, {'Proven.Allowed'})

    def test_nested_comments_and_string_messages(self):
        self.assertFalse(check_source('Human.Example', '''
/- unsafe /- partial -/ sorry -/
-- @[extern "foreign"]
def message := "An axiom is not a proof."
def json := r#"{"text": "/-"}"#
''', set()))

    def test_generated_unsafe_code_needs_permission(self):
        with self.assertRaisesRegex(ValueError, 'unlisted'):
            check_source('Human.Example', 'def code := "unsafe def f := 0"', set())
        with self.assertRaisesRegex(ValueError, 'unlisted'):
            check_source('Human.Example', 'def code := s!"{unsafe evalExpr Nat type value}"', set())

    def test_unlisted_external_library_fails(self):
        graph = {'Human.Example': ['Other.Library'], 'Other.Library': []}
        with self.assertRaisesRegex(ValueError, 'Other.Library'):
            check_graph(graph, ['Human.Example'], {'Lean', 'Mathlib'})

    def test_manifest_contains_the_native_binding(self):
        self.assertIn('Human.Import.NativeGrid', manifest_list('trustedTacticModules'))
        self.assertIn('SailRV32', manifest_list('trustedModuleRoots'))


if __name__ == '__main__':
    unittest.main()
