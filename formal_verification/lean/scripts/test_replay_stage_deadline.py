"""Exercise the workflow's replay scheduling wrapper without launching Lean."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import textwrap
import unittest


WORKFLOW = (Path(__file__).resolve().parents[3] /
            '.github/workflows/formal-verification.yml')


class ReplayStageDeadline(unittest.TestCase):
    def setUp(self):
        self.workflow = WORKFLOW.read_text()
        self.stage = self.workflow.split('        id: kernel-replay\n', 1)[1].split(
            '      - name:', 1)[0]
        self.maximum = int(re.search(r'fv_stage kernel-replay (\d+) ', self.stage)[1])
        self.wrapper = textwrap.dedent(self.workflow.split(
            '          fv_stage() {\n', 1)[1].split('          fv_limited() {', 1)[0])
        self.wrapper = 'fv_stage() {\n' + self.wrapper

    def run_stage(self, remaining, timeout_exit=0):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, contents in {
                'date': '#!/bin/sh\necho 1000\n',
                'timeout': '#!/bin/sh\nprintf "%s\\n" "$@" > "$FIXTURE_CALL"\n'
                           'exit "$FIXTURE_TIMEOUT_EXIT"\n',
            }.items():
                tool = root / name
                tool.write_text(contents)
                tool.chmod(0o755)
            call = root / 'call'
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH'],
                       FV_WORK_DEADLINE=str(1000 + remaining), FIXTURE_CALL=str(call),
                       FIXTURE_TIMEOUT_EXIT=str(timeout_exit))
            script = ('set -euo pipefail\n' + self.wrapper +
                      f'fv_stage kernel-replay {self.maximum} python3 fixture.py\n')
            result = subprocess.run(['bash', '-c', script], env=env,
                                    text=True, capture_output=True)
            return result, call.read_text().splitlines() if call.exists() else None

    def test_complete_replay_has_room_within_the_existing_job_boundary(self):
        self.assertEqual(self.maximum, 18 * 60 * 60)
        outer_minutes = int(re.search(r'timeout-minutes: (\d+)', self.stage)[1])
        self.assertGreaterEqual(outer_minutes * 60, self.maximum + 120)
        self.assertIn('timeout-minutes: 1440', self.workflow)
        self.assertIn('22 * 60 * 60', self.workflow)
        result, call = self.run_stage(22 * 60 * 60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(call, ['--signal=TERM', '--kill-after=120s', '64800s',
                                'python3', 'fixture.py'])

    def test_shared_work_deadline_still_clips_replay(self):
        result, call = self.run_stage(600)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(call[2], '600s')

    def test_cleanup_reserve_prevents_a_new_launch(self):
        for remaining in (120, 0, -1):
            with self.subTest(remaining=remaining):
                result, call = self.run_stage(remaining)
                self.assertEqual(result.returncode, 124)
                self.assertIsNone(call)

    def test_timeout_failure_is_propagated(self):
        result, call = self.run_stage(600, timeout_exit=124)
        self.assertEqual(result.returncode, 124)
        self.assertEqual(call[2], '600s')


if __name__ == '__main__':
    unittest.main()
