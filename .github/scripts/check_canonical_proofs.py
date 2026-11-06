#!/usr/bin/env python3
"""Check the canonical circuit/mode inventory and every regenerated file byte."""

import json
from pathlib import Path
import sys


def load_inventory(path):
    entries = json.loads(Path(path).read_text())
    assert len(entries) == 28, "expected 14 circuits in both soundness modes"
    keys = {(entry["circuit"], entry["soundness_mode"]) for entry in entries}
    circuits = {circuit for circuit, _ in keys}
    modes = {"pessimistic_conjecture", "ethproofs_soundcalc"}
    assert len(circuits) == 14 and len(keys) == len(entries)
    assert keys == {(circuit, mode) for circuit in circuits for mode in modes}
    names = [entry["proof_file"] for entry in entries]
    assert len(set(names)) == len(names), "duplicate canonical proof filename"
    assert all(Path(name).name == name for name in names), names
    gpu_tests = [entry["gpu_test"] for entry in entries]
    assert len(set(gpu_tests)) == len(gpu_tests), "duplicate canonical GPU test name"
    for entry in entries:
        assert entry["gpu_test"] == (
            f"tests::proof_matrix::canonical_{entry['circuit']}_{entry['soundness_mode']}"
        ), entry
    return set(names)


def check_inventory(directory, expected):
    directory = Path(directory)
    actual = {
        path.name
        for path in directory.glob("*_gkr_proof.json")
        if not path.name.startswith("malicious_")
    }
    assert actual == expected, {
        "directory": str(directory),
        "missing": sorted(expected - actual),
        "extra": sorted(actual - expected),
    }


def main():
    assert len(sys.argv) in (3, 4), "MANIFEST COMMITTED_DIR [REGENERATED_DIR]"
    expected = load_inventory(sys.argv[1])
    committed = Path(sys.argv[2])
    check_inventory(committed, expected)
    if len(sys.argv) == 3:
        print("Canonical proof inventory: exactly 28 circuit/mode files")
        return
    regenerated = Path(sys.argv[3])
    check_inventory(regenerated, expected)
    changed = [
        name
        for name in sorted(expected)
        if (committed / name).read_bytes() != (regenerated / name).read_bytes()
    ]
    assert not changed, {"canonical proof bytes changed": changed}
    print("Canonical proofs are current: 28 byte-identical circuit/mode files")


if __name__ == "__main__":
    main()
