import json
from pathlib import Path
import re
import tempfile
import unittest

from check_axioms import analyze
from check_lean import direct_axioms
import check_review


class AxiomReportTests(unittest.TestCase):
    def test_public_review_theorem_requires_an_explicit_unique_audit_request(self):
        module = 'Airbender.Review.Trace.Workers.Keccak.SplitPermutation'
        name = 'Airbender.Keccak.Split.Native.permutation_soundness'
        source = check_review.ROOT.joinpath(*module.split('.')).with_suffix('.lean')
        for number, line in enumerate(source.read_text().splitlines(), 1):
            match = re.match(r'theorem permutation_soundness\b', line)
            if match:
                break
        else:
            self.fail('The public split permutation statement was not found')
        # Match the compiled inventory's source range through the theorem name.
        record = f'REVIEW_THEOREM {module} {name} {number} 0 {number} {match.end()}\n'
        audit = check_review.ROOT / 'Airbender/Checks/Axioms.lean'
        self.assertEqual(check_review.check_theorems(record, audit), 1)
        request = f'#print axioms {name}\n'
        original = audit.read_text()
        self.assertEqual(original.count(request), 1)
        with tempfile.TemporaryDirectory() as directory:
            specimen = Path(directory) / 'Axioms.lean'
            specimen.write_text(original.replace(request, ''))
            with self.assertRaisesRegex(ValueError, 'Missing public theorem audit roots'):
                check_review.check_theorems(record, specimen)
            specimen.write_text(original + request)
            with self.assertRaisesRegex(ValueError, 'Duplicate axiom audit roots'):
                check_review.check_theorems(record, specimen)

    def test_public_baseline_retires_internal_roots_but_protects_review(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = {'roots': ['Fixture'], 'reviewPrefix': 'Review'}
            records = [
                {'kind': 'header', 'schema': 'airbender-proof-audit-v1',
                 'explicitRoots': 1, 'reviewPrefix': 'Review'},
                {'kind': 'root', 'name': 'Fixture', 'origin': 'Review',
                 'explicit': True, 'proofValued': True},
                {'kind': 'declaration', 'name': 'Fixture', 'declarationKind': 'theorem',
                 'origin': 'Review', 'unsafe': False, 'partial': False, 'uses': []},
                {'kind': 'footer', 'roots': 1, 'declarations': 1},
            ]
            report = root / 'inventory.jsonl'
            report.write_text(''.join(json.dumps(record) + '\n' for record in records))
            baseline = {'commit': 'fixture', 'roots': {'Fixture': [], 'OldShard': []},
                        'protected_roots': ['Fixture']}
            result = analyze(report, request, baseline, root / 'retired')
            self.assertTrue(result['passed'])
            self.assertEqual(result['retired_internal_roots'], ['OldShard'])
            baseline['roots']['MissingReview'] = []
            baseline['protected_roots'].append('MissingReview')
            result = analyze(report, request, baseline, root / 'missing-review')
            self.assertFalse(result['passed'])
            self.assertEqual(result['missing_baseline_roots'], ['MissingReview'])

    def test_direct_report_difference_is_informational_but_inventory_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Airbender/Checks').mkdir(parents=True)
            (root / 'scripts').mkdir()
            (root / 'Airbender/Checks/Axioms.lean').write_text('#print axioms Fixture\n')
            (root / 'scripts/axiom_baseline.json').write_text(json.dumps({
                'commit': 'fixture', 'roots': {'Fixture': ['propext'], 'Review.InventoryOnly': []}}))
            log = root / 'smoke.log'
            log.write_text("'Fixture' does not depend on any axioms\n")
            direct_axioms(root, log, root / 'result.json')
            self.assertTrue(json.loads((root / 'result.json').read_text())['passed'])
            log.write_text('')
            with self.assertRaises(ValueError):
                direct_axioms(root, log, root / 'result.json')

    def test_direct_smoke_accepts_multiline_standard_axioms(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Airbender/Checks').mkdir(parents=True)
            (root / 'scripts').mkdir()
            (root / 'Airbender/Checks/Axioms.lean').write_text('#print axioms Fixture\n')
            (root / 'scripts/axiom_baseline.json').write_text(json.dumps({
                'commit': 'fixture', 'roots': {'Review.InventoryOnly': []}}))
            log = root / 'smoke.log'
            log.write_text("'Fixture' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n")
            direct_axioms(root, log, root / 'result.json')
            result = json.loads((root / 'result.json').read_text())
            self.assertEqual(result['roots'], {'Fixture': ['Classical.choice', 'Quot.sound', 'propext']})
            self.assertTrue(result['passed'])

    def test_direct_smoke_rejects_missing_extra_duplicate_and_forbidden_reports(self):
        valid = "'Fixture' does not depend on any axioms\n"
        cases = [
            ('missing', '', False, 'missing_source_reports'),
            ('extra', valid + "'Extra' does not depend on any axioms\n", False, 'extra_reports'),
            ('duplicate-report', valid + valid, False, 'duplicate_reports'),
            ('duplicate-source', valid, True, 'duplicate_source_roots'),
            ('forbidden', "'Fixture' depends on axioms: [sorryAx]\n", False, 'forbidden_axioms'),
        ]
        for name, text, duplicate_source, field in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / 'Airbender/Checks').mkdir(parents=True)
                (root / 'scripts').mkdir()
                (root / 'Airbender/Checks/Axioms.lean').write_text(
                    '#print axioms Fixture\n' * (2 if duplicate_source else 1))
                (root / 'scripts/axiom_baseline.json').write_text(json.dumps({
                    'commit': 'fixture', 'roots': {'Fixture': [], 'Review.InventoryOnly': []}}))
                log = root / 'smoke.log'
                log.write_text(text)
                with self.assertRaises(ValueError):
                    direct_axioms(root, log, root / 'result.json')
                self.assertTrue(json.loads((root / 'result.json').read_text())[field])

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
