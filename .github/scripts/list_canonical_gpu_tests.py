#!/usr/bin/env python3
"""List the compiled canonical matrix and check it against the shared recipe."""

import os
from pathlib import Path
import subprocess
import sys


def validate_names(expected, actual):
    assert len(expected) == len(set(expected)) == 28, expected
    assert len(actual) == len(set(actual)) == 28, actual
    assert set(actual) == set(expected), {
        "missing": sorted(set(expected) - set(actual)),
        "extra": sorted(set(actual) - set(expected)),
    }


def main():
    binary = str(Path(sys.argv[1]).resolve())
    output = Path(sys.argv[2])
    expected_path = output.with_suffix(".expected.txt")
    expected_path.unlink(missing_ok=True)
    listing = subprocess.check_output(
        [binary, "--list", "--ignored", "tests::proof_matrix::canonical_"],
        text=True,
    )
    output.write_text(listing)
    env = os.environ.copy()
    env["AB_GPU_CANONICAL_TEST_NAMES"] = str(expected_path.resolve())
    inventory = subprocess.check_output(
        [binary, "--exact", "tests::proof_matrix::cpu_canonical_matrix_inventory", "--test-threads=1"],
        env=env,
        text=True,
    )
    assert "1 passed; 0 failed; 0 ignored;" in inventory, inventory
    expected = expected_path.read_text().splitlines()
    actual = [line.removesuffix(": test") for line in listing.splitlines() if line.endswith(": test")]
    validate_names(expected, actual)
    print("Selected exactly 28 canonical circuit/mode tests")


if __name__ == "__main__":
    main()
