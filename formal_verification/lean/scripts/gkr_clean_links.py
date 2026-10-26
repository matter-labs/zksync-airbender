#!/usr/bin/env python3
"""Bind actual native arithmetic to each retained higher-level Clean artifact."""
import argparse
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES

MODELS = ['AddSub', 'JumpBranchSlt', 'MulDiv', 'ShiftBinop', 'WordMemory', 'SubwordMemory',
          'UnifiedReduced', 'Bigint', 'Blake2G', 'Blake2Round', 'Keccak']
WIDTHS = [None, None, None, None, 9, 9, 10, 3, 9, 6, 8]


def module(case, model, width):
    target = 'Airbender.Proofs.GKRProtocol.CleanLinksNative.' + case
    namespace = 'Airbender.Compiler.CleanLinksNative.' + case
    native = 'Airbender.Compiler.CleanArithmeticNative.' + case + '.native'
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    binder = f'(setup : Table Source.BaseField (fields {width})) ' if width else ''
    setup = 'setup ' if width else ''
    operations = f'(Airbender.{model}.importedConstraints (p := babyBearModulus){" setup" if width else ""})'
    clock_operations = f'(Airbender.{model}.clockConstraints (p := babyBearModulus){" setup" if width else ""})'
    content = (f'import Airbender.Proofs.GKRProtocol.CleanBindings\nimport Airbender.Proofs.GKRProtocol.CleanArithmeticNative.{case}\n'
        f'import Airbender.Review.Circuits.{model}.Artifact\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'theorem arithmetic_inventory {binder}:\n'
        f'    FlatOperation.constraints {operations} = {native}.expressions := by rfl\n\n'
        f'theorem retained_constraints {binder}(base : GKRAddress → Source.BaseField)\n'
        '    (data : ProverData Source.BaseField)\n'
        f'    (arithmetic : ∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (base ∘ {base}.bank.address) = 0)\n'
        f'    (primitives : ∀ lookup ∈ FlatOperation.lookups {operations}, lookup.Contains ({native}.environment base data)) :\n'
        f'    FlatOperation.ConstraintsHoldFlat ({native}.environment base data) {operations} :=\n'
        f'  CleanExpression.retained_constraints {operations} {native}.expressions\n'
        f'    (arithmetic_inventory {setup}) ({native}.environment base data)\n'
        f'    ({native}.arithmetic_preserved base data arithmetic) primitives\n\n'
        f'theorem clock_arithmetic_inventory {binder}:\n'
        f'    FlatOperation.constraints {clock_operations} = {native}.expressions := by rfl\n\n'
        f'theorem retained_clock_constraints {binder}(base : GKRAddress → Source.BaseField)\n'
        '    (data : ProverData Source.BaseField)\n'
        f'    (arithmetic : ∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (base ∘ {base}.bank.address) = 0)\n'
        f'    (primitives : ∀ lookup ∈ FlatOperation.lookups {clock_operations}, lookup.Contains ({native}.environment base data)) :\n'
        f'    FlatOperation.ConstraintsHoldFlat ({native}.environment base data) {clock_operations} :=\n'
        f'  CleanExpression.retained_constraints {clock_operations} {native}.expressions\n'
        f'    (clock_arithmetic_inventory {setup}) ({native}.environment base data)\n'
        f'    ({native}.arithmetic_preserved base data arithmetic) primitives\n\n'
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
    for family, stem, model, width in zip(FAMILIES, CASES, MODELS, WIDTHS, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            target, content = module(stem + mode.title(), model, width)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('retained Clean arithmetic binding changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(family + '-' + mode, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
