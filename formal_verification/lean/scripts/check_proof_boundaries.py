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
# These four adapters instantiate generic Review predicates with artifact data.
# Their Import closures include generated native definitions and certificates in
# Proofs; only their direct imports are restricted. The remaining compiler
# semantics modules have the stronger transitive check below. This import check
# does not validate artifact interpretation or every instantiated premise.
COMPILER_BINDINGS = frozenset({
    'Airbender.Review.Compiler.Pooled',
    'Airbender.Review.Compiler.Unified',
    'Airbender.Review.Compiler.LogicalRows',
    'Airbender.Review.Compiler.Program',
})
# These public-program adapters instantiate the same native row and setup
# types. Their import closures include native arithmetic certificates. Keep
# direct Proofs imports and supporting theorems forbidden in these records.
PROGRAM_BINDINGS = frozenset({
    'Airbender.Review.Compiler.ProgramLogicalRows',
    'Airbender.Review.Compiler.NativePublicSetup',
    'Airbender.Review.Compiler.NativeSubwordSetup',
    'Airbender.Review.Compiler.NativeMachineArguments',
})


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
    check_compiler_layout()
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


def check_compiler_semantics(root):
    """Reject calculations hidden behind an intermediate semantic import."""
    for name, path in closure(root):
        if name.startswith('Airbender.Proofs.'):
            raise ValueError('compiler semantics import calculations: ' + ' -> '.join(path))


def compatibility_reexport(name, source):
    """Accept only the four exact legacy import shims. They define no semantics."""
    if name not in COMPILER_BINDINGS:
        return False
    expected = name.replace('Airbender.Review.Compiler.',
                            'Airbender.Proofs.Compatibility.Compiler.', 1)
    body = '\n'.join(line.split('--', 1)[0].strip() for line in source.splitlines()).strip()
    return body == 'import ' + expected


def check_compiler_layout():
    """Check semantic definitions transitively and artifact bindings directly."""
    for legacy in ('GKRCompiler', 'GKRProtocol'):
        if (ROOT / legacy).exists() or (ROOT / (legacy + '.lean')).exists():
            raise ValueError('compiler module outside Review/Import/Proofs: ' + legacy)
    for name, path in MODULES.items():
        if not name.startswith('Airbender.Review.Compiler.') or name.endswith('.Theorems'):
            continue
        source = path.read_text()
        if compatibility_reexport(name, source):
            continue
        if re.search(r'^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s', source, re.M):
            raise ValueError('supporting theorem in compiler review definitions: ' + name)
        for dependency in IMPORTS[name]:
            if dependency.startswith('Airbender.Proofs.'):
                raise ValueError('compiler definitions import calculations: ' + name + ' -> ' + dependency)
        if name not in COMPILER_BINDINGS | PROGRAM_BINDINGS:
            check_compiler_semantics(name)
    for name, path in MODULES.items():
        if name.startswith(('Airbender.Proofs.GKRCompiler.', 'Airbender.Proofs.GKRProtocol.')):
            if re.search(r'^(?:syntax|elab_rules|elab)\b', path.read_text(), re.M):
                raise ValueError('compiler reader/elaborator belongs in Import: ' + name)


if __name__ == '__main__':
    try:
        cores, workers = check()
        print(f'PASS {cores} definition/core boundaries and {workers} local worker boundaries')
    except (OSError, ValueError) as error:
        raise SystemExit(f'FAIL {error}') from error
