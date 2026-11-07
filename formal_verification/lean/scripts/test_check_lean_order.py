"""Early witnesses must retain the complete, dependency-correct source inventory."""
import unittest

from check_lean import ordered, prioritized_order


class SourceOrder(unittest.TestCase):
    def test_priorities_build_their_dependency_closures_before_unrelated_sources(self):
        imports = {
            'A.Unrelated': ['Shared'], 'B.Dep': ['Shared', 'Mathlib.External'],
            'Shared': [], 'Tests.First': ['B.Dep'], 'Tests.Second': ['Shared'],
            'Z.Final': ['Tests.First', 'A.Unrelated'],
        }
        order = prioritized_order(imports, imports, ['Tests.First', 'Tests.Second'])
        self.assertEqual(order[:4], ['Shared', 'B.Dep', 'Tests.First', 'Tests.Second'])
        self.assertEqual(set(order), set(imports))
        self.assertEqual(len(order), len(imports))
        for user, dependencies in imports.items():
            for dependency in set(dependencies) & imports.keys():
                self.assertLess(order.index(dependency), order.index(user))

    def test_import_dependencies_take_precedence_over_requested_priority_order(self):
        imports = {'First': ['Second'], 'Second': [], 'Other': []}
        self.assertEqual(prioritized_order(imports, imports, ['First', 'Second']),
                         ['Second', 'First', 'Other'])

    def test_no_priority_preserves_existing_order(self):
        imports = {'A': [], 'B': ['A'], 'C': []}
        self.assertEqual(prioritized_order(imports, imports), ordered(imports, imports))

    def test_unknown_duplicate_and_cyclic_requests_are_rejected(self):
        imports = {'A': [], 'B': ['A']}
        for priorities in (['Missing'], ['A', 'A']):
            with self.subTest(priorities=priorities), self.assertRaises(ValueError):
                prioritized_order(imports, imports, priorities)
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            prioritized_order(['A', 'B'], {'A': ['B'], 'B': ['A']}, ['A'])


if __name__ == '__main__':
    unittest.main()
