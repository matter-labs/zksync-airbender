#!/usr/bin/env python3
"""Check the pinned v2 circuit/native inputs and unchanged reused sources."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent

def check():
    record = json.loads((ROOT / "artifacts/provenance.json").read_text())
    groups = ("reused_files", "current_v3_reused_files", "circuit_artifacts", "native_sources", "setup_artifacts", "native_exporter_files")
    for group in groups:
        for entry in record[group]:
            path = ROOT / entry["path"]
            if hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
                raise ValueError(f"changed pinned {group}: {entry['path']}")
    return (len(record["reused_files"]) + len(record["current_v3_reused_files"]),
            len(record["circuit_artifacts"]), len(record["native_sources"]))

if __name__ == "__main__":
    try:
        reused, artifacts, native = check()
        print(f"PASS {reused} reused files, {artifacts} circuit artifacts, {native} native sources")
    except (ValueError, OSError) as error:
        raise SystemExit(f"FAIL {error}") from error
