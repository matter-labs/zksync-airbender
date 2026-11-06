import json
from argparse import Namespace
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from bounded_fv import parse_args
from check_axioms import run_guarded, sha, write_json
from check_kernel_replay import REPLAY_REVIEW_MODULES, cached_json, run_replay, valid_inventory, valid_replay
from check_lean import SOURCE_REVIEW_TARGETS


class ReplayCacheTests(unittest.TestCase):
    def inventory(self):
        return {'schema': 'airbender-kernel-replay-v1', 'module': 'Fixture',
                'files': ['workspace/Fixture.olean'], 'safe': ['Fixture.proof'],
                'dependencies': [{'user': 'Fixture.proof', 'uses': ['True']}],
                'imports': [{'module': 'Init', 'importAll': False, 'isExported': True, 'isMeta': False}],
                'skipped': [], 'skippedDependencyUses': [], 'codegenOnly': [], 'axioms': [], 'isModule': False}

    def test_interrupted_inventory_is_a_miss_and_atomic_replacement_recovers(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'inventory.json'
            path.write_text('{"schema":')
            self.assertIsNone(cached_json(path))
            self.assertFalse(valid_inventory(cached_json(path), 'Fixture', {'workspace/Fixture.olean': 'hash'}))
            inventory = self.inventory()
            write_json(path, inventory)
            self.assertTrue(valid_inventory(cached_json(path), 'Fixture', {'workspace/Fixture.olean': 'hash'}))
            self.assertEqual(list(Path(directory).iterdir()), [path])

    def test_incomplete_nested_inventory_is_a_cache_miss(self):
        for field, value in (
            ('dependencies', [{'user': 'Fixture.proof'}]),
            ('dependencies', [{'user': 'Fixture.proof', 'uses': [None]}]),
            ('imports', [{'module': 'Init'}]),
            ('skipped', [{'name': 'Fixture.unsafe', 'unsafe': True}]),
            ('skipped', [{'name': 'Fixture.unsafe', 'unsafe': 1, 'partial': False}]),
            ('skippedDependencyUses', [{'user': 'Fixture.proof'}]),
            ('codegenOnly', [None]),
        ):
            with self.subTest(field=field, value=value):
                inventory = self.inventory()
                inventory[field] = value
                self.assertFalse(valid_inventory(inventory, 'Fixture', {'workspace/Fixture.olean': 'hash'}))

    def test_cached_pass_binds_declaration_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory)
            inventory = self.inventory()
            report = {**inventory, 'status': 'pass'}
            report_path = ledger / 'passed' / 'key.report.json'
            write_json(report_path, report)
            record = {'key': 'key', 'module': 'Fixture', 'status': 'pass', 'parts': {},
                      'safe': inventory['safe'], 'dependencies': {}, 'guard': {'passed': True},
                      'report': report_path.name, 'report_sha256': sha(report_path)}
            self.assertTrue(valid_replay(record, 'Fixture', 'key', {}, inventory, {}, ledger))
            changed = deepcopy(inventory)
            changed['dependencies'][0]['uses'] = []
            self.assertFalse(valid_replay(record, 'Fixture', 'key', {}, changed, {}, ledger))

    def test_invalid_or_missing_replay_record_never_passes(self):
        with tempfile.TemporaryDirectory() as directory:
            ledger = Path(directory)
            for value in (None, {}, {'report': '../../escape'}, {'report': 'missing.json'}):
                self.assertFalse(valid_replay(value, 'Fixture', 'key', {}, {}, {}, ledger))

    def test_only_the_exact_chi_replay_gets_the_existing_review_allowance(self):
        chi = 'Airbender.Proofs.FullUnsigned.Source.ChiCharacters'
        self.assertEqual(REPLAY_REVIEW_MODULES, {chi})
        self.assertEqual(SOURCE_REVIEW_TARGETS, {'+' + chi + ':olean'})
        modules = [chi, chi + 'Extra', chi + '.Nested',
                   'Airbender.Proofs.FullUnsigned.Source.ParityCharacters']
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sysroot, compiled = root / 'sysroot', root / 'compiled'
            library = sysroot / 'lib/lean'
            files = {}
            for module in ['Lean.Replay', *modules]:
                base = library if module == 'Lean.Replay' else compiled
                files[module] = base.joinpath(*module.split('.')).with_suffix('.olean')
                files[module].parent.mkdir(parents=True, exist_ok=True)
                files[module].write_text(module)
            calls = []

            def inventory(module):
                data = self.inventory()
                data.update(module=module, files=[str(files[module])],
                            safe=[module + '.proof'], dependencies=[{
                                'user': module + '.proof', 'uses': []}],
                            imports=[] if module == 'Lean.Replay' else [{
                                'module': 'Lean.Replay', 'importAll': False,
                                'isExported': True, 'isMeta': False}])
                return data

            def guarded(_root, _guard, _sysroot, _directory, label, command, **kwargs):
                calls.append((label, kwargs))
                mode = command[-2] if label == 'search-path' else command[-3]
                output = Path(command[-1])
                if mode == 'paths':
                    write_json(output, list(map(str, [library, compiled])))
                else:
                    module = command[-2]
                    data = inventory(module)
                    if mode == 'replay':
                        data['status'] = 'pass'
                    write_json(output, data)
                return {'passed': True}

            args = Namespace(root=root, output=root / 'output', ledger=root / 'ledger',
                             sysroot=sysroot, guard=root / 'guard.py', extra_path=[],
                             module=modules, fresh_project=True, stack_mib=2048, axiom_result=None)
            with patch('check_kernel_replay.tool_identity', return_value={}), \
                    patch('check_kernel_replay.run_guarded', side_effect=guarded):
                result = run_replay(args)
            self.assertTrue(result['passed'])
            self.assertEqual([label for label, options in calls if options['review']],
                             ['replay-' + chi])
            self.assertEqual(len([label for label, _ in calls if label.startswith('replay-')]), 5)
            self.assertTrue(all(options['stack_mib'] == (2048 if sys.platform == 'linux' else None)
                                for _, options in calls))

    def test_guard_commands_keep_caps_and_reject_an_unsuccessful_review_child(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            guard = root / 'fake_guard.py'
            guard.write_text('import json, sys\n'
                             'print(json.dumps({"reason": "finished", "exit": 0, '
                             '"live_owned_after": []}))\n')
            for review, seconds in [(False, 900), (True, 1800)]:
                label = 'review' if review else 'normal'
                result = run_guarded(root, guard, root, root / 'jobs', label,
                                     [sys.executable, '-c', 'pass'], stack_mib=2048, review=review)
                self.assertTrue(result['passed'])
                command = json.loads((root / 'jobs' / (label + '.command.json')).read_text())['command']
                parsed = parse_args(command[2:])
                self.assertEqual((parsed.mib, parsed.resident_mib, parsed.seconds, parsed.stack_mib),
                                 (2560, 5120, seconds, 2048))
                self.assertEqual(parsed.review, review)
                self.assertFalse(parsed.native_artifact)
            guard.write_text('import json, sys\n'
                             'print(json.dumps({"reason": "wall-time budget exceeded", '
                             '"exit": 125, "live_owned_after": []}))\n'
                             'sys.exit(125)\n')
            with self.assertRaisesRegex(RuntimeError, 'bounded worker/API/resource failure'):
                run_guarded(root, guard, root, root / 'jobs', 'failed-review',
                            [sys.executable, '-c', 'pass'], stack_mib=2048, review=True)
            failed = json.loads((root / 'jobs/failed-review.result.json').read_text())
            self.assertFalse(failed['passed'])


if __name__ == '__main__':
    unittest.main()
