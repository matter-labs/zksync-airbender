import json
from copy import deepcopy
from pathlib import Path
import tempfile
import unittest

from check_axioms import sha, write_json
from check_kernel_replay import cached_json, valid_inventory, valid_replay


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


if __name__ == '__main__':
    unittest.main()
