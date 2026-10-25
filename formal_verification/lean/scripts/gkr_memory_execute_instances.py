#!/usr/bin/env python3
"""Bind the source memory execution mask to canonical helper history normalization."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_full_arithmetic_certificate import synthesize
from gkr_wiring_instances import CASES


def module(name, case):
    root = LEAN / 'artifacts/compiler'
    arity = len(synthesize(json.loads((root / (name + '.json')).read_text()),
                           json.loads((root / (name + '-source.json')).read_text()))['inputs'])
    target = 'GKRProtocol.MemoryExecuteNative.' + case
    namespace = 'Airbender.Compiler.MemoryExecuteNative.' + case
    models = [('base_model', 'FullArithmeticNative'), ('memory_model', 'MemoryNative'),
              ('helper_model', 'HelperValidityNative'), ('helper_fields', 'HelperNative'),
              ('frame_model', 'MemoryFrameNative')]
    content = (f'import GKRProtocol.MemoryExecuteImport\nimport GKRProtocol.MemoryFrameNative.{case}\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        'import_memory_execute native\n' +
        ''.join('  ' + key + ' Airbender.Compiler.' + model + '.' + case + '.native\n' for key, model in models) +
        f'  inputs {arity}\n\nend {namespace}\n')
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
            name, case = family + '-' + mode, stem + mode.title()
            target, content = module(name, case)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('source memory execute binding changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
