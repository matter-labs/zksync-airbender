"""Sail drift checks must observe changed, deleted and added generated files."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().with_name('lean-ci.sh')


class SailDriftTest(unittest.TestCase):
    def test_generated_diff_is_not_restored(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'sail').mkdir()
            (root / 'lean/sail-rv32/SailRV32').mkdir(parents=True)
            (root / 'lean/sail-rv32/SailRV32.lean').write_text('import SailRV32.Defs\n')
            (root / 'lean/sail-rv32/SailRV32/Defs.lean').write_text('def value := 1\n')
            (root / 'lean/sail-rv32/lake-manifest.json').write_text('{}')
            regen = root / 'sail/regen.sh'
            regen.write_text('''#!/bin/bash
set -eu
rm -f "$FV_DIR/lean/sail-rv32/lake-manifest.json"
case "$FV_TEST_DRIFT" in
 changed) echo 'def value := 2' > "$FV_DIR/lean/sail-rv32/SailRV32/Defs.lean" ;;
 deleted) rm "$FV_DIR/lean/sail-rv32/SailRV32/Defs.lean" ;;
 added) echo 'def extra := 0' > "$FV_DIR/lean/sail-rv32/SailRV32/Extra.lean" ;;
esac
''')
            regen.chmod(0o755)
            def git(*args):
                subprocess.run(['git', '-C', str(root), *args], check=True, capture_output=True)
            git('init', '-q')
            git('add', '.')
            git('-c', 'user.name=FV Test', '-c', 'user.email=fv@example.invalid',
                '-c', 'commit.gpgsign=false', 'commit', '-qm', 'fixture')
            for mode in ('same', 'changed', 'deleted', 'added'):
                git('restore', '--source=HEAD', '--worktree', '.')
                (root / 'lean/sail-rv32/SailRV32/Extra.lean').unlink(missing_ok=True)
                result = subprocess.run(['bash', str(SCRIPT), 'sail-gen'],
                                        env=dict(os.environ, FV_DIR=str(root), FV_TEST_DRIFT=mode),
                                        capture_output=True, text=True)
                with self.subTest(mode=mode):
                    self.assertEqual(result.returncode == 0, mode == 'same', result.stdout + result.stderr)
                    self.assertTrue((root / 'lean/sail-rv32/lake-manifest.json').exists())


if __name__ == '__main__':
    unittest.main()
