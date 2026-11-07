"""Review snapshots must cover configured runtime roots and all library sources."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from check_lean import discover
import check_review


class ReviewBuildInventory(unittest.TestCase):
    def fixture(self, root):
        for name in ('Airbender.lean', 'Airbender/Model.lean', 'Tests/Check.lean',
                     'generated/sail-rv32/Sail/Model.lean', 'runtime/Tools/Oracle.lean',
                     'scripts/Unconfigured.lean'):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('')
        (root / 'lakefile.toml').write_text('''
[[lean_exe]]
name = "tests"
root = "Tests.Check"
[[lean_exe]]
name = "oracle"
root = "Tools.Oracle"
srcDir = "runtime"
''')

    def test_actual_project_inventory_includes_every_configured_executable(self):
        sources = check_review.current_project_sources(check_review.ROOT)
        self.assertEqual(sources, discover(check_review.ROOT))
        self.assertEqual(sources['scripts.ProgramRowsOracle'],
                         check_review.ROOT / 'scripts/ProgramRowsOracle.lean')

    def test_srcdir_is_resolved_and_unconfigured_tooling_is_excluded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.fixture(root)
            sources = check_review.current_project_sources(root)
            self.assertEqual(set(sources), {'Airbender', 'Airbender.Model', 'Tests.Check',
                                            'Sail.Model', 'Tools.Oracle'})
            self.assertEqual(sources['Tools.Oracle'], root / 'runtime/Tools/Oracle.lean')

    def test_missing_and_conflicting_runtime_sources_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.fixture(root)
            oracle = root / 'runtime/Tools/Oracle.lean'
            oracle.unlink()
            with self.assertRaisesRegex(ValueError, 'Missing current project source'):
                check_review.current_project_sources(root)
            oracle.write_text('')
            with (root / 'lakefile.toml').open('a') as stream:
                stream.write('[[lean_exe]]\nname="conflict"\nroot="Tests.Check"\nsrcDir="runtime"\n')
            with self.assertRaisesRegex(ValueError, 'Conflicting current executable source'):
                check_review.current_project_sources(root)

    def test_snapshot_cannot_drop_or_invent_a_source_object_or_import_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            self.fixture(root)
            sources = check_review.current_project_sources(root)
            for field in ('sources', 'objects', 'imports'):
                for mutation in ('drop', 'extra'):
                    with self.subTest(field=field, mutation=mutation):
                        snapshot = {'schema': 'airbender-serial-build-v2',
                                    'root': str(root), 'complete_project': True}
                        snapshot.update({key: dict.fromkeys(sources, {})
                                         for key in ('sources', 'objects', 'imports')})
                        if mutation == 'drop':
                            del snapshot[field]['Tools.Oracle']
                        else:
                            snapshot[field]['scripts.Unconfigured'] = {}
                        path = root / 'snapshot.json'
                        path.write_text(json.dumps(snapshot))
                        with patch.object(check_review, 'ROOT', root), self.assertRaisesRegex(
                                ValueError, 'Incomplete current project ' + field + ' inventory'):
                            check_review.verify_build_snapshot(path)


if __name__ == '__main__':
    unittest.main()
