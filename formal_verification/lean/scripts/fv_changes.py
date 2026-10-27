#!/usr/bin/env python3
"""Select FV runs from pinned evidence and the native producer's Cargo closure."""
import argparse
import json
from pathlib import Path
import subprocess

from check_setup_artifacts import REPO, source_inventory


def relevant(path, pins, crates):
    if path.startswith(('formal_verification/', '.cargo/', 'cs/compiled_circuits/')):
        return True
    if path in pins or path in {'.github/workflows/ci.yml', '.github/workflows/formal-verification.yml',
                                 'Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml'}:
        return True
    return any(path.startswith(crate + '/') and
               (path.endswith('.rs') or path == crate + '/Cargo.toml') for crate in crates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True)
    parser.add_argument('--head', default='HEAD')
    args = parser.parse_args()
    try:
        paths, crates = source_inventory(REPO)
        pins = set(paths)
        for relative, key in [('formal_verification/lean/artifacts/setup/native-evidence.json', 'sources'),
                              ('formal_verification/lean/artifacts/setup/manifest.json', 'source_sha256')]:
            pins.update(json.loads((REPO / relative).read_text())[key])
        if not args.base.strip('0'):
            print('true')
            return
        changed = subprocess.check_output(['git', 'diff', '--name-only', '-z', args.base, args.head], cwd=REPO)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError):
        # A broken/partially edited producer inventory needs FV, not a skip.
        print('true')
        return
    print('true' if any(relevant(path, pins, crates) for path in changed.decode().split('\0') if path) else 'false')


if __name__ == '__main__':
    main()
