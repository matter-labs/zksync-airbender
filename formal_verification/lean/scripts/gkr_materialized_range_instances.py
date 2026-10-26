#!/usr/bin/env python3
"""Bind full literal setup data and constructive counts to each native layout."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES


def module(family, stem, mode):
    case = stem + mode.title()
    target = 'Airbender.Proofs.GKRProtocol.MaterializedRangeNative.' + case
    namespace = 'Airbender.Compiler.MaterializedRangeNative.' + case
    model = 'Airbender.Compiler.MaterializedNative.' + case + '.native.model'
    content = (f'import Airbender.Import.GKRProtocol.MaterializedRangeImport\nimport Airbender.Proofs.GKRProtocol.MaterializedNative.{case}\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n'
        f'import_materialized_ranges native model {model}\n\n'
        f'end {namespace}\n')
    return target, content


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            target, content = module(family, stem, mode)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('materialized setup binding changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(family + '-' + mode, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
