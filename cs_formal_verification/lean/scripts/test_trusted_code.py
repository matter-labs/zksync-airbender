"""Regressions for reviewed module permissions and source checks."""
import unittest
from check_import_closure import check_graph, check_sail_edges
from check_trusted_code import check_declaration_commands, check_source, manifest_edges, manifest_list


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
                     'example : True := by native_decide', 'example : True := by bv_decide',
                     'set_option debug.skipKernelTC true in\ntheorem bad : False := sorryAx False',
                     'run_cmd Lean.addDeclWithoutChecking decl']:
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

    def test_declaration_commands_need_the_exact_list(self):
        sources = {'Human.Command': 'elab "emit" : command => pure ()', 'Human.Plain': 'def plain := 0',
                   'Human.Decl': 'def emit : CoreM Unit := addDecl declaration',
                   'Human.Comment': '-- elab_rules : command\ndef message := "addDecl"'}
        check_declaration_commands(sources, {'Human.Command', 'Human.Decl'})
        with self.assertRaisesRegex(ValueError, 'Unlisted declaration command modules: Human.Decl'):
            check_declaration_commands(sources, {'Human.Command'})
        with self.assertRaisesRegex(ValueError, 'define no declaration commands: Human.Plain'):
            check_declaration_commands(sources, {'Human.Command', 'Human.Decl', 'Human.Plain'})

    def test_sail_model_only_in_listed_modules(self):
        graph = {'Human.Sail': ['Sail.Model'], 'Human.Claims': ['Human.Sail'], 'Human.Other': [],
                 'Sail.Model': []}
        check_graph(graph, ['Human.Sail', 'Human.Claims', 'Human.Other'], {'Sail'}, {'Human.Sail', 'Human.Claims'})
        with self.assertRaisesRegex(ValueError, 'Sail import boundary: Human.Claims → Human.Sail → Sail.Model'):
            check_graph(graph, ['Human.Sail', 'Human.Claims'], {'Sail'}, {'Human.Sail'})
        with self.assertRaisesRegex(ValueError, 'do not import the Sail model: Human.Other'):
            check_graph(graph, ['Human.Sail', 'Human.Other'], {'Sail'}, {'Human.Sail', 'Human.Other'})

    def test_direct_sail_imports_need_the_exact_edges(self):
        graph = {'Human.Helpers.Core.Configuration': ['SailRV32'], 'Human.ISA.Sail.Theorems':
                 ['Human.Helpers.Core.Configuration', 'SailRV32.Functions'], 'Proven.Sail.Bytes': ['SailRV32'],
                 'SailRV32': [], 'SailRV32.Functions': []}
        listed = {('Human.Helpers.Core.Configuration', 'SailRV32'), ('Proven.Sail.Bytes', 'SailRV32')}
        with self.assertRaisesRegex(ValueError, 'Unlisted direct Sail import: Human.ISA.Sail.Theorems → SailRV32.Functions'):
            check_sail_edges(graph, listed)
        check_sail_edges(graph, listed | {('Human.ISA.Sail.Theorems', 'SailRV32.Functions')})
        with self.assertRaisesRegex(ValueError, 'Listed Sail import is absent: Proven.Other → Sail'):
            check_sail_edges(graph, listed | {('Human.ISA.Sail.Theorems', 'SailRV32.Functions'), ('Proven.Other', 'Sail')})

    def test_unlisted_external_library_fails(self):
        graph = {'Human.Example': ['Other.Library'], 'Other.Library': []}
        with self.assertRaisesRegex(ValueError, 'Other.Library'):
            check_graph(graph, ['Human.Example'], {'Lean', 'Mathlib'})

    def test_manifest_contains_the_native_binding(self):
        self.assertIn('Human.Import.SetupEmit', manifest_list('trustedTacticModules'))
        self.assertIn('SailRV32', manifest_list('trustedModuleRoots'))
        self.assertIn('Human.Import.TranscribeCommand', manifest_list('declarationCommandModules'))
        self.assertIn('Human.Helpers.Core.Configuration', manifest_list('sailModules'))
        self.assertIn(('Human.Helpers.Core.Configuration', 'SailRV32'), manifest_edges('sailImportEdges'))


if __name__ == '__main__':
    unittest.main()
