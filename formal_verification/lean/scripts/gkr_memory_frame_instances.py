#!/usr/bin/env python3
"""Check canonical source memory frames against actual finite and external native ports."""
import argparse
import json
import os
import re
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_full_arithmetic_certificate import synthesize
from gkr_wiring_instances import CASES


def ram_count(case):
    source = (LEAN / 'Airbender/Proofs/GKRProtocol/MemoryNative' / (case + '.lean')).read_text()
    data = json.loads(json.loads(re.search(r'selectors ("(?:[^"\\]|\\.)*")', source).group(1)))
    return 7 * sum(len(data['groups'][stem]['source_labels']) for stem in ['memoryRead', 'memoryWrite'])


def module(name, case, phase=3, start=0, stop=None):
    root = LEAN / 'artifacts/compiler'
    arity = len(synthesize(json.loads((root / (name + '.json')).read_text()),
                           json.loads((root / (name + '-source.json')).read_text()))['inputs'])
    size = ram_count(case)
    if stop is None:
        stop = size
    suffix = 'Inputs' if phase == 0 else 'Part' + str(start // 64) if phase == 1 else ''
    target = 'Airbender.Proofs.GKRProtocol.MemoryFrameNative.' + case + suffix
    namespace = 'Airbender.Compiler.MemoryFrameNative.' + case
    prefix = 'Airbender.Compiler.'
    models = [('base_model', 'FullArithmeticNative'), ('memory_model', 'MemoryNative'),
              ('source_model', 'SourceContractNative'), ('history_model', 'HistoryErasureNative'),
              ('helper_model', 'HelperValidityNative'), ('counter_model', 'CounterFrameNative')]
    imports = f'import Airbender.Import.GKRProtocol.MemoryFrameImport\nimport Airbender.Proofs.GKRProtocol.CounterFrameNative.{case}\n'
    if phase in [1, 2]:
        imports += f'import Airbender.Proofs.GKRProtocol.MemoryFrameNative.{case}Inputs\n'
    if phase == 2:
        imports += ''.join(f'import Airbender.Proofs.GKRProtocol.MemoryFrameNative.{case}Part{index}\n' for index in range((size + 63) // 64))
    content = (imports + '\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_memory_frame native from "artifacts/compiler/{name}-source.json"\n' +
        ''.join('  ' + key + ' ' + prefix + model + '.' + case + '.native\n' for key, model in models) +
        f'  inputs {arity} phase {phase} start {start} stop {stop}\n\nend {namespace}\n')
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
            size = ram_count(case)
            phases = [(3, 0, size)] if size <= 256 else ([(0, 0, size)] +
                [(1, first, min(first + 64, size)) for first in range(0, size, 64)] + [(2, 0, size)])
            for phase, start, stop in phases:
                target, content = module(name, case, phase, start, stop)
                path = LEAN / (target.replace('.', '/') + '.lean')
                if args.check and (not path.exists() or path.read_text() != content):
                    raise ValueError('source memory frame changed: ' + target)
                if args.write and (not path.exists() or path.read_text() != content):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(content)
                print(name, flush=True)
                if args.build:
                    subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                        cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
