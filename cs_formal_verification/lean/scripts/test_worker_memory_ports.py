#!/usr/bin/env python3
"""Regressions for the worker memory module generator."""
from pathlib import Path
import subprocess
import sys
import unittest

SCRIPT = Path(__file__).resolve().parent / "generate_worker_memory_ports.py"


def run(*arguments):
    return subprocess.run([sys.executable, str(SCRIPT), *arguments], text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


class WorkerMemoryPortTests(unittest.TestCase):
    def test_unknown_worker_name_fails(self):
        result = run("--check", "DoesNotExist")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FAIL unknown worker names: DoesNotExist", result.stdout)

    def test_known_worker_name_is_checked(self):
        result = run("--check", "Bigint")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("PASS worker memory modules", result.stdout)


if __name__ == "__main__":
    unittest.main()
