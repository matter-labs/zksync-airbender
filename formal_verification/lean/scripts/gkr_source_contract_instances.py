#!/usr/bin/env python3
"""Instantiate source-clock/borrow witness extension, one native profile at a time."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_full_arithmetic_certificate import synthesize


def module(name, case):
    root = LEAN / 'artifacts/compiler'
    pair = json.loads((root / (name + '.json')).read_text())
    snapshot = json.loads((root / (name + '-source.json')).read_text())
    arity = len(synthesize(pair, snapshot)['inputs'])
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    graph = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    lookup = 'Airbender.Compiler.LookupNative.' + case + '.native'
    product = 'Airbender.Compiler.ProductNative.' + case + '.native'
    target = 'GKRProtocol.SourceContractNative.' + case
    namespace = 'Airbender.Compiler.SourceContractNative.' + case
    content = (f'import GKRProtocol.SourceContractImport\nimport GKRProtocol.FunctionalNative.{case}\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_compiler_source_contract native from "artifacts/compiler/{name}.json"\n'
        f'  source "artifacts/compiler/{name}-source.json" base_model {base} inputs {arity}\n\n'
        'theorem source_contract_graph_extends {R : Type} [CommRing R]\n'
        '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
        f'    (sourceValue : Fin {base}.inputs.length → Source.BaseField)\n'
        '    (original : Satisfies (native.originals.map Expression.polynomial) sourceValue)\n'
        f'    (clockValid : Source.clockContract native.clock ({base}.helperPlacement.memory.project sourceValue))\n'
        '    (fallback : GKRAddress → Source.BaseField) :\n'
        f'    ∃ sourceExtended : Fin {base}.inputs.length → Source.BaseField,\n'
        '      (∀ index, (∀ borrow, native.slots borrow ≠ index) → sourceExtended index = sourceValue index) ∧\n'
        '      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,\n'
        f'        (∀ wire, baseValue ({base}.inputBank.address wire) = sourceExtended wire) ∧\n'
        f'        (∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (baseValue ∘ {base}.bank.address) = 0) ∧\n'
        f'        (∀ address, {graph}.isBase address = true → values address = hom (baseValue address)) ∧\n'
        f'        (∀ definition ∈ {graph}.definitions, definition.Holds hom challenges values) ∧\n'
        f'        (∀ gate ∈ {lookup}.gates, gate.Holds hom challenges gamma values) ∧\n'
        f'        (∀ gate ∈ {product}.gates, gate.Holds hom challenges values) := by\n'
        '  obtain ⟨sourceExtended, frame, holds⟩ := native.source_contract_extension sourceValue original clockValid\n'
        '  refine ⟨sourceExtended, frame, ?_⟩\n'
        f'  exact {graph}.full_graph_extends hom challenges gamma sourceExtended holds fallback\n\n'
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
                raise ValueError('source contract scaffold changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
