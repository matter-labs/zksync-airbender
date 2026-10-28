import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import fv_changes
from fv_changes import relevant


class ChangeSelection(unittest.TestCase):
    def test_proof_tools_evidence_and_new_native_sources(self):
        for path in ('formal_verification/lean/README.md', 'cs/src/gkr_compiler/new.rs',
                     'cs/Cargo.toml', 'cs/generated/new.rs', 'cs/examples/export_gkr_translation.rs',
                     'Cargo.lock', '.cargo/config.toml', '.github/workflows/formal-verification.yml',
                     'shared/pinned.bin'):
            self.assertTrue(relevant(path, {'shared/pinned.bin'}, ['cs']), path)

    def test_unrelated_changes_do_not_start_fv(self):
        for path in ('README.md', 'cli/src/main.rs', 'cs/README.md', 'docs/rust.md'):
            self.assertFalse(relevant(path, set(), ['cs']), path)

    def test_invalid_evidence_or_diff_selects_verification(self):
        for invalid_manifest in (True, False):
            with self.subTest(invalid_manifest=invalid_manifest), patch('sys.argv', ['fv_changes.py', '--base', 'HEAD^']), patch.object(
                    fv_changes, 'source_inventory', return_value=([], [])), patch.object(
                    fv_changes.Path, 'read_text', return_value='{' if invalid_manifest else '{"sources": [], "source_sha256": []}'), patch.object(
                    fv_changes.subprocess, 'check_output', side_effect=subprocess.CalledProcessError(1, ['git'])):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    fv_changes.main()
                self.assertEqual(output.getvalue().strip(), 'true')

    def test_moving_a_relevant_file_out_of_the_tree_still_selects_verification(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            def git(*args):
                return subprocess.check_output(['git', '-c', 'user.name=Fixture', '-c',
                    'user.email=fixture@example.invalid', *args], cwd=repo, stderr=subprocess.DEVNULL)
            git('init', '-q')
            source = repo / 'formal_verification/fixture.txt'
            source.parent.mkdir()
            source.write_text('identical contents for rename detection\n')
            git('add', '.')
            git('commit', '-qm', 'fixture before rename')
            source.rename(repo / 'README.md')
            git('add', '-A')
            git('commit', '-qm', 'fixture after rename')
            metadata = repo / 'formal_verification/lean/artifacts/setup'
            metadata.mkdir(parents=True)
            (metadata / 'native-evidence.json').write_text('{"sources": {}}')
            (metadata / 'manifest.json').write_text('{"source_sha256": {}}')
            output = io.StringIO()
            with patch('sys.argv', ['fv_changes.py', '--base', 'HEAD^']), patch.object(
                    fv_changes, 'REPO', repo), patch.object(fv_changes, 'source_inventory',
                    return_value=([], [])), contextlib.redirect_stdout(output):
                fv_changes.main()
            self.assertEqual(output.getvalue().strip(), 'true')


if __name__ == '__main__':
    unittest.main()
