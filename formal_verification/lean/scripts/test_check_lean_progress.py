"""Progress polling must preserve a real child's complete output and failure."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from check_lean import communicate_with_progress


class LeanProgress(unittest.TestCase):
    def test_progress_releases_child_and_preserves_output_and_nonzero_exit(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'release'
            child = subprocess.Popen([
                sys.executable, '-c',
                'import pathlib,sys,time\n'
                'print("before",flush=True)\n'
                'marker=pathlib.Path(sys.argv[1]); deadline=time.monotonic()+5\n'
                'while not marker.exists() and time.monotonic()<deadline: time.sleep(.01)\n'
                'print("after",file=sys.stderr,flush=True)\n'
                'sys.exit(7 if marker.exists() else 9)\n', str(marker)],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            calls = []

            def progress():
                calls.append(True)
                marker.touch()

            try:
                output, error = communicate_with_progress(child, progress, interval=.02)
                self.assertTrue(calls)
                self.assertEqual(output, 'before\nafter\n')
                self.assertIsNone(error)
                self.assertEqual(child.returncode, 7)
            finally:
                if child.poll() is None:
                    child.kill()
                    child.wait()

    def test_progress_failure_remains_an_exception_for_existing_child_cleanup(self):
        class PendingChild:
            def communicate(self, *, timeout):
                raise subprocess.TimeoutExpired('pending', timeout)

        def progress():
            raise InterruptedError('interrupted')

        with self.assertRaises(InterruptedError):
            communicate_with_progress(PendingChild(), progress)


if __name__ == '__main__':
    unittest.main()
