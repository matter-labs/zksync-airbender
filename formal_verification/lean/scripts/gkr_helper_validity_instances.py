#!/usr/bin/env python3
"""Check source primitive contracts imply all actual native helper query memberships."""
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
    target = 'GKRProtocol.HelperValidityNative.' + case
    namespace = 'Airbender.Compiler.HelperValidityNative.' + case
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    source = 'Airbender.Compiler.SourceContractNative.' + case + '.native'
    graph = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    helper = 'Airbender.Compiler.HelperNative.' + case + '.native'
    lookup = 'Airbender.Compiler.LookupNative.' + case + '.native'
    product = 'Airbender.Compiler.ProductNative.' + case + '.native'
    content = (f'import GKRProtocol.HelperValidityImport\nimport GKRProtocol.HistoryErasureNative.{case}\nimport GKRProtocol.HelperNative.{case}\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_helper_validity native from "artifacts/compiler/{name}-source.json"\n'
        f'  base_model Airbender.Compiler.FullArithmeticNative.{case}.native\n'
        f'  source_model Airbender.Compiler.SourceContractNative.{case}.native\n  history_model Airbender.Compiler.HistoryErasureNative.{case}.native\n  helper_model Airbender.Compiler.HelperNative.{case}.native\n  memory_model Airbender.Compiler.MemoryNative.{case}.native inputs {arity}\n\n'
        'theorem helper_graph_extends {R : Type} [CommRing R]\n'
        '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
        f'    (sourceValue : Fin {arity} → Source.BaseField)\n'
        f'    (original : Satisfies ({source}.originals.map Expression.polynomial) sourceValue)\n'
        f'    (clockValid : Source.clockContract {source}.clock ({base}.helperPlacement.memory.project sourceValue))\n'
        f'    (primitives : native.profile.ExecutionValid (native.execute.value ({base}.helperPlacement.memory.project sourceValue))\n'
        f'      ({base}.helperPlacement.memory.project sourceValue)) (fallback : GKRAddress → Source.BaseField) :\n'
        '    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,\n'
        f'      (∀ wire, baseValue ({base}.inputBank.address wire) = native.canonical sourceValue wire) ∧\n'
        f'      (∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (baseValue ∘ {base}.bank.address) = 0) ∧\n'
        f'      (∀ address, {graph}.isBase address = true → values address = hom (baseValue address)) ∧\n'
        f'      (∀ definition ∈ {graph}.definitions, definition.Holds hom challenges values) ∧\n'
        f'      (∀ gate ∈ {lookup}.gates, gate.Holds hom challenges gamma values) ∧\n'
        f'      (∀ gate ∈ {product}.gates, gate.Holds hom challenges values) ∧\n'
        f'      (∀ field ∈ {helper}.fields, (field.value ({helper}.sourceValues baseValue)).val < 524288) := by\n'
        f'  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products⟩ :=\n'
        f'    {graph}.full_graph_extends hom challenges gamma (native.canonical sourceValue)\n'
        '      (native.source_holds sourceValue original clockValid) fallback\n'
        '  exact ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products,\n'
        '    native.native_helper_membership sourceValue primitives baseValue inputAgreement⟩\n\n'
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
            target, content = module(name, case)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('helper validity scaffold changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
