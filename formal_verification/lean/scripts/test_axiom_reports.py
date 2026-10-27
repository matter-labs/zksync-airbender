import json
from pathlib import Path
import tempfile
import unittest

from check_axioms import analyze
from check_lean import direct_axioms


class AxiomReportTests(unittest.TestCase):
    def test_direct_report_difference_is_informational_but_inventory_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Airbender/Checks').mkdir(parents=True)
            (root / 'scripts').mkdir()
            (root / 'Airbender/Checks/Axioms.lean').write_text('#print axioms Fixture\n')
            (root / 'scripts/axiom_baseline.json').write_text(json.dumps({'commit': 'fixture', 'roots': {'Fixture': ['propext']}}))
            log = root / 'smoke.log'
            log.write_text("'Fixture' does not depend on any axioms\n")
            direct_axioms(root, log, root / 'result.json')
            self.assertTrue(json.loads((root / 'result.json').read_text())['passed'])
            log.write_text('')
            with self.assertRaises(ValueError):
                direct_axioms(root, log, root / 'result.json')

    def test_environment_constructor_dependency_requires_an_exact_disposition(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = {'roots': ['Fixture'], 'reviewPrefix': 'Review'}
            declarations = [('Fixture', 'inductive', ['Fixture.mk']),
                            ('Fixture.mk', 'constructor', ['propext']), ('propext', 'axiom', [])]
            records = [{'kind': 'header', 'schema': 'airbender-proof-audit-v1', 'explicitRoots': 1, 'reviewPrefix': 'Review'},
                       {'kind': 'root', 'name': 'Fixture', 'origin': 'Review', 'explicit': True, 'proofValued': False}]
            records += [{'kind': 'declaration', 'name': name, 'declarationKind': kind,
                         'origin': 'Review' if name != 'propext' else 'Init',
                         'unsafe': False, 'partial': False, 'uses': uses} for name, kind, uses in declarations]
            records.append({'kind': 'footer', 'roots': 1, 'declarations': 3})
            report = root / 'inventory.jsonl'
            report.write_text(''.join(json.dumps(record) + '\n' for record in records))
            baseline = {'commit': 'fixture', 'roots': {'Fixture': []}}
            result = analyze(report, request, baseline, root / 'first')
            self.assertEqual(result['axioms']['Fixture'], ['propext'])
            self.assertFalse(result['passed'])
            disposition = {'Fixture': {'before': [], 'after': ['propext'], 'reason': 'constructor field dependency'}}
            self.assertTrue(analyze(report, request, baseline, root / 'second', disposition)['passed'])


if __name__ == '__main__':
    unittest.main()
