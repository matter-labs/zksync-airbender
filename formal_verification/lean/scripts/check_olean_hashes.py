#!/usr/bin/env python3
"""Recompute compiled file hashes and bind them to Lake's recorded trace outputs.

Run inside the existing resource guard, after ordinary Lake freshness checks.
This is artifact-integrity checking, not proof replay or source elaboration.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess


def recorded_hash(path):
    path = Path(path)
    match = re.search(r'\.olean(?:\.server|\.private)?$', str(path))
    if match is None:
        raise ValueError('Not a compiled Lean artifact: ' + str(path))
    suffix = match.group()
    trace = Path(str(path)[:match.start()] + '.trace')
    outputs = json.loads(trace.read_text())['outputs']['o']
    matches = [item[:-len(suffix)] for item in outputs if isinstance(item, str) and item.endswith(suffix)]
    if len(matches) != 1 or re.fullmatch(r'[0-9a-f]{16}', matches[0]) is None:
        raise ValueError('Missing/ambiguous compiled output hash: ' + str(trace))
    return matches[0]


def verify(paths, reports):
    actual = {}
    for record in reports:
        if record['path'] in actual:
            raise ValueError('Duplicate recomputed artifact hash')
        actual[record['path']] = record['hash']
    if set(actual) != set(paths):
        raise ValueError('Recomputed artifact inventory differs from request')
    for path in paths:
        expected = recorded_hash(path)
        sidecar = Path(path + '.hash')
        if actual[path] != expected or (sidecar.is_file() and sidecar.read_text().strip() != expected):
            raise ValueError('Compiled artifact differs from its Lake trace: ' + path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    paths = json.loads(args.request.read_text())
    helper = Path(__file__).with_name('HashOleanFiles.lean')
    result = subprocess.run(['lake', 'env', 'lean', '--run', str(helper), str(args.request)],
                            text=True, capture_output=True, check=True)
    reports = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
    verify(paths, reports)
    args.output.write_text(json.dumps({'passed': True, 'files': reports}, indent=2) + '\n')


if __name__ == '__main__':
    main()
