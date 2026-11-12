#!/usr/bin/env python3
"""Drift guard for the circuit JSONs the spec imports (human/ via import_clean).

For every cs/compiled_circuits JSON named in lakefile.toml:
  - the bytes match the sha256 pinned in circuit_json_pins.json (an intended change
    means updating the pin in the same commit);
  - the JSON has no duplicate object keys (the Lean importer would otherwise keep one
    silently) and no nonfinite numbers;
  - no two imported circuits have the same canonical content (a duplicated circuit).
For every setup JSON named in lakefile.toml (artifacts/setup/), and for the circuit JSONs too:
  - the bytes are the file's canonical form: setup JSONs compact (the exporter's output,
    `json.dumps(v, separators=(",", ":"))`), circuit JSONs serde_json's pretty form
    (`json.dumps(v, indent=2)`), no trailing newline. The importer parses every byte in the
    interpreter, so a re-indented setup JSON would cost the build seconds of whitespace.
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


def setup_paths():
    text = (ROOT / "lakefile.toml").read_text()
    names = sorted(set(re.findall(r'"(artifacts/setup/[A-Za-z0-9_.-]+\.json)"', text)))
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


# The canonical form of each kind of JSON: description, json.dumps arguments, the same as Python source.
SETUP_FORM = ("compact", {"separators": (",", ":")}, 'separators=(",", ":")')
CIRCUIT_FORM = ("serde_json pretty, indent 2", {"indent": 2}, "indent=2")


def load(raw):
    return json.loads(raw, object_pairs_hook=reject_duplicates, parse_constant=reject_constant)


def check_form(path, rel, raw, data, form, errors):
    """The file is `json.dumps(data, **form)`, byte for byte (no trailing newline)."""
    description, kwargs, source = form
    if json.dumps(data, **kwargs).encode() != raw:
        command = (f"python3 -c 'import json,sys; p=sys.argv[1]; d=json.load(open(p)); "
                   f"open(p,\"w\").write(json.dumps(d, {source}))' {path}")
        errors.append(f"{rel}: not in canonical form ({description}); canonicalize with:\n  {command}")


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
        raw = path.read_bytes()
        try:
            data = load(raw)
        except ValueError as exc:
            errors.append(f"{rel}: {exc}")
            continue
        check_form(path, rel, raw, data, CIRCUIT_FORM, errors)
        digest = hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if digest in seen_digest:
            errors.append(f"{rel}: same circuit content as {seen_digest[digest]}")
        seen_digest.setdefault(digest, rel)
    setups = setup_paths()
    if not setups:
        errors.append("no setup JSON found in lakefile.toml")
    for path in setups:
        rel = path.relative_to(REPO).as_posix()
        if not path.is_file():
            errors.append(f"{rel}: missing")
            continue
        raw = path.read_bytes()
        try:
            data = load(raw)
        except ValueError as exc:
            errors.append(f"{rel}: {exc}")
            continue
        check_form(path, rel, raw, data, SETUP_FORM, errors)
    stale = sorted(set(pins) - {p.relative_to(REPO).as_posix() for p in paths})
    if stale:
        errors.append(f"pins for JSONs no longer imported: {stale}")
    for error in errors:
        print(f"FAIL: {error}")
    if errors:
        return 1
    print(f"circuit JSON: {len(paths)} imported, pinned, no duplicate keys, no duplicate circuits, canonical form")
    print(f"setup JSON: {len(setups)} imported, no duplicate keys, canonical form (compact)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
