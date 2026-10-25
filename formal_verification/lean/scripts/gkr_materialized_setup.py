#!/usr/bin/env python3
"""Import actual full materialized setup columns with tracked Airbender inputs."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def module(family, case):
    artifact = json.loads((LEAN / 'artifacts/setup' / (family + '.json')).read_text())
    target = 'Airbender.Data.GKRSetup.' + case
    content = (f'import Airbender.Import.GKRSetupEmbed\n\nnamespace {target}\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n'
        f'import_full_setup setup from "artifacts/setup/{family}.json"\n\n'
        f'theorem trace_length : setup.data.length = {artifact["trace_len"]} := rfl\n'
        'theorem range16_length : setup.range16.length = setup.data.length := rfl\n'
        'theorem timestamp_length : setup.timestampRange.length = setup.data.length := rfl\n\n'
        f'end {target}\n')
    return target, content


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, case in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        target, content = module(family, case)
        path = LEAN / (target.replace('.', '/') + '.lean')
        if args.check and (not path.exists() or path.read_text() != content):
            raise ValueError('materialized setup scaffold changed: ' + target)
        if args.write and (not path.exists() or path.read_text() != content):
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        print(family, flush=True)
        if args.build:
            subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
