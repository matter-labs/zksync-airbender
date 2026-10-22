#!/usr/bin/env python3
"""Check the proof-reuse import boundaries without running a compiler."""
from collections import deque
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODULES = {
    '.'.join(path.relative_to(ROOT).with_suffix('').parts): path
    for path in (ROOT / 'Airbender').rglob('*.lean')
}
IMPORTS = {
    name: re.findall(r'^(?:(?:public|meta)\s+)*import(?:\s+all)?\s+(\S+)', path.read_text(), re.M)
    for name, path in MODULES.items()
}
CORES = (
    'Airbender.Proofs.Arithmetic.FieldSliceDefinitions',
    'Airbender.Proofs.Arithmetic.ExpressionRows',
    'Airbender.Proofs.Blake2G.AssemblyDefinitions',
    'Airbender.Proofs.Blake2G.FrameDefinitions',
    'Airbender.Proofs.Blake2G.FrameNormalization',
    'Airbender.Proofs.Blake2G.FrameQueryEntries',
    'Airbender.Proofs.Blake2G.FrameQueryValues',
    'Airbender.Proofs.Blake2G.FrameQueryArithmetic',
    'Airbender.Proofs.Blake2G.FrameQueryRows',
    'Airbender.Proofs.Constraints.Core',
)
LOCAL_WORKERS = (
    'Airbender.Proofs.Blake2G.PhysicalStep',
    'Airbender.Proofs.Keccak.Phases.IotaPart0',
    'Airbender.Proofs.Blake2G.NativeEffects',
    'Airbender.Proofs.Keccak.NativeEffects',
)


def closure(root):
    pending = deque([(root, [root])])
    seen = set()
    while pending:
        name, path = pending.popleft()
        if name in seen:
            continue
        seen.add(name)
        yield name, path
        pending.extend((dep, [*path, dep]) for dep in IMPORTS.get(name, ()))


def check():
    for core in CORES:
        if core not in MODULES:
            raise ValueError(f'missing core: {core}')
        for name, path in closure(core):
            if (name.startswith('Airbender.Import.') or
                    (name.startswith('Airbender.') and
                     any(part in name.split('.') for part in ('Artifact', 'NativeExecution')))):
                raise ValueError('core imports parser/native implementation: ' + ' -> '.join(path))
    for worker in LOCAL_WORKERS:
        for name, path in closure(worker):
            if (name in ('Airbender.Proofs.Delegation.Operations',
                         'Airbender.Review.Trace.Delegation.Theorems') or
                    name.startswith('Airbender.Proofs.Blake2Round.NativeDiagonalQueries')):
                raise ValueError('worker imports composed operation proof: ' + ' -> '.join(path))
    return len(CORES), len(LOCAL_WORKERS)


if __name__ == '__main__':
    try:
        cores, workers = check()
        print(f'PASS {cores} definition/core boundaries and {workers} local worker boundaries')
    except (OSError, ValueError) as error:
        raise SystemExit(f'FAIL {error}') from error
