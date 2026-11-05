#!/usr/bin/env python3
"""Drift guard for the circuit JSONs the spec imports (human/ via import_clean).

For every cs/compiled_circuits JSON named in lakefile.toml:
  - the bytes match the sha256 pinned in circuit_json_pins.json (an intended change
    means updating the pin in the same commit);
  - the JSON has no duplicate object keys (the Lean importer would otherwise keep one
    silently) and no nonfinite numbers;
  - no two imported circuits have the same canonical content (a duplicated circuit).
Python 3.11+ is not required. Run from any directory.
"""

from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
PINS = ROOT / "circuit_json_pins.json"


def imported_paths():
    text = (ROOT / "lakefile.toml").read_text()
    names = sorted(set(re.findall(r'"((?:\.\./)+cs/compiled_circuits/[A-Za-z0-9_.-]+\.json)"', text)))
    return [(ROOT / name).resolve() for name in names]


def reject_duplicates(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError(f"nonfinite JSON number {value}")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    errors = []
    paths = imported_paths()
    if not paths:
        errors.append("no imported circuit JSON found in lakefile.toml")
    pins = json.loads(PINS.read_text()) if PINS.exists() else {}
    seen_digest = {}
    for path in paths:
        rel = path.relative_to(REPO).as_posix()
        if not path.is_file():
            errors.append(f"{rel}: missing")
            continue
        if pins.get(rel) != sha256(path):
            errors.append(f"{rel}: sha256 differs from circuit_json_pins.json")
        try:
            data = json.loads(path.read_text(), object_pairs_hook=reject_duplicates,
                              parse_constant=reject_constant)
        except ValueError as exc:
            errors.append(f"{rel}: {exc}")
            continue
        digest = hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if digest in seen_digest:
            errors.append(f"{rel}: same circuit content as {seen_digest[digest]}")
        seen_digest.setdefault(digest, rel)
    stale = sorted(set(pins) - {p.relative_to(REPO).as_posix() for p in paths})
    if stale:
        errors.append(f"pins for JSONs no longer imported: {stale}")
    for error in errors:
        print(f"FAIL: {error}")
    if errors:
        return 1
    print(f"circuit JSON: {len(paths)} imported, pinned, no duplicate keys, no duplicate circuits")
    return 0


if __name__ == "__main__":
    sys.exit(main())
