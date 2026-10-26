#!/usr/bin/env python3
"""Check authored query preservation through canonical native witness construction."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_full_arithmetic_certificate import synthesize
from gkr_wiring_instances import CASES


def module(name, case, phase=3, start=0, stop=None):
    root = LEAN / 'artifacts/compiler'
    arity = len(synthesize(json.loads((root / (name + '.json')).read_text()),
                           json.loads((root / (name + '-source.json')).read_text()))['inputs'])
    size = sum(len(row['fields']) for row in json.loads((root / 'lookup' / (name + '.json')).read_text())['rows'])
    if stop is None:
        stop = size
    suffix = 'Inputs' if phase == 0 else 'Part' + str(start // 64) if phase == 1 else ''
    target = 'Airbender.Proofs.GKRProtocol.QueryFrameNative.' + case + suffix
    namespace = 'Airbender.Compiler.QueryFrameNative.' + case
    prefix = 'Airbender.Compiler.'
    pair = json.loads((root / (name + '.json')).read_text())
    query_names = []
    for kind in pair['circuit']['global_output_map']:
        stem = {'GenericLookup': 'generic', 'Lookup16Bits': 'range16'}.get(kind)
        if stem:
            query_names.append(prefix + 'LookupSourceNative.' + case + '.native.' + stem + 'Queries')
    query_term = ' ++ '.join(query_names) or '[]'
    imports = f'import Airbender.Import.GKRProtocol.QueryFrameImport\nimport Airbender.Proofs.GKRProtocol.CounterFrameNative.{case}\n'
    if phase in [1, 2]:
        imports += f'import Airbender.Proofs.GKRProtocol.QueryFrameNative.{case}Inputs\n'
    if phase == 2:
        imports += ''.join(f'import Airbender.Proofs.GKRProtocol.QueryFrameNative.{case}Part{index}\n' for index in range((size + 63) // 64))
    content = (imports + '\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_query_frame native certificate "artifacts/compiler/lookup/{name}.json"\n'
        f'  queries ({query_term})\n'
        f'  base_model {prefix}FullArithmeticNative.{case}.native\n'
        f'  lookup_model {prefix}LookupNative.{case}.native\n'
        f'  query_model {prefix}LookupSourceNative.{case}.native\n'
        f'  source_model {prefix}SourceContractNative.{case}.native\n'
        f'  history_model {prefix}HistoryErasureNative.{case}.native\n'
        f'  helper_model {prefix}HelperValidityNative.{case}.native\n'
        f'  counter_model {prefix}CounterFrameNative.{case}.native inputs {arity} phase {phase} start {start} stop {stop}\n\n'
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
            name, case = family + '-' + mode, stem + mode.title()
            size = sum(len(row['fields']) for row in json.loads((LEAN / 'artifacts/compiler/lookup' / (name + '.json')).read_text())['rows'])
            phases = [(3, 0, size)] if size <= 256 else ([(0, 0, size)] +
                [(1, first, min(first + 64, size)) for first in range(0, size, 64)] + [(2, 0, size)])
            for phase, start, stop in phases:
                target, content = module(name, case, phase, start, stop)
                path = LEAN / (target.replace('.', '/') + '.lean')
                if args.check and (not path.exists() or path.read_text() != content):
                    raise ValueError('query frame changed: ' + target)
                if args.write and (not path.exists() or path.read_text() != content):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(content)
                print(name, flush=True)
                if args.build:
                    subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                        cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
