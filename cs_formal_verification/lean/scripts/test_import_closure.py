"""Reject each Lean import form, including transitive imports and Clean."""
from pathlib import Path
import tempfile
import unittest
from check_import_closure import check_graph, load_graph


class ImportClosureTest(unittest.TestCase):
    def test_real_parser_finds_all_import_forms(self):
        forms = ['import Checks.Bad', 'public import Checks.Bad', 'meta import Checks.Bad',
                 'public meta import Checks.Bad', 'import all Checks.Bad',
                 'import Init import Checks.Bad']
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Human').mkdir()
            (root / 'Checks').mkdir()
            (root / 'Checks/Bad.lean').write_text('module\n')
            for index, form in enumerate(forms):
                (root / f'Human/Bad{index}.lean').write_text('module\n' + form + '\n')
            names = [f'Human.Bad{i}' for i in range(len(forms))]
            graph = load_graph(names, root)
            for name in names:
                with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'Checks.Bad'):
                    check_graph(graph, [name])

    def test_transitive_and_clean_boundaries(self):
        for target in ['Proven.Bad', 'Tests.Bad', 'Checks.Bad', 'Clean.Spec']:
            graph = {'Human.A': ['Helper'], 'Helper': [target], target: []}
            with self.assertRaisesRegex(ValueError, 'Human.A → Helper'):
                check_graph(graph, ['Human.A'])
        graph = {'CleanCore.Equivalence': ['Clean.Spec'], 'Clean.Spec': []}
        check_graph(graph, ['CleanCore.Equivalence'])
        graph['Human.A'] = ['CleanCore.Equivalence']
        with self.assertRaises(ValueError):
            check_graph(graph, ['Human.A'])


if __name__ == '__main__':
    unittest.main()
