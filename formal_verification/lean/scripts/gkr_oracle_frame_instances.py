#!/usr/bin/env python3
"""Construct native graphs with chosen setup values and lookup multiplicities."""
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
    target = 'Airbender.Proofs.GKRProtocol.OracleFrameNative.' + case
    namespace = 'Airbender.Compiler.OracleFrameNative.' + case
    prefix = 'Airbender.Compiler.'
    base = prefix + 'FullArithmeticNative.' + case + '.native'
    source = prefix + 'SourceContractNative.' + case + '.native'
    helper = prefix + 'HelperValidityNative.' + case + '.native'
    fields = prefix + 'HelperNative.' + case + '.native'
    counter = prefix + 'CounterFrameNative.' + case + '.native'
    table = prefix + 'TableNative.' + case + '.native'
    model = prefix + 'MaterializedNative.' + case + '.native.model'
    memory = prefix + 'MemoryNative.' + case + '.native'
    graph = prefix + 'FunctionalNative.' + case + '.native'
    lookup = prefix + 'LookupNative.' + case + '.native'
    product = prefix + 'ProductNative.' + case + '.native'
    typing = prefix + 'ConsumerNative.' + case + '.native.typing'
    content = (f'import Airbender.Import.GKRProtocol.OracleFrameImport\nimport Airbender.Proofs.GKRProtocol.CounterFrameNative.{case}\nimport Airbender.Proofs.GKRProtocol.MaterializedNative.{case}\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_lookup_oracle_frame native from "artifacts/compiler/{name}.json"\n'
        f'  base_model {base} typing {typing}\n\n'
        'theorem oracle_graph_extends {R : Type} [CommRing R]\n'
        '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
        f'    (sourceValue : Fin {arity} → Source.BaseField)\n'
        f'    (original : Satisfies ({source}.originals.map Expression.polynomial) sourceValue)\n'
        f'    (clockValid : Source.clockContract {source}.clock ({base}.helperPlacement.memory.project sourceValue))\n'
        f'    (primitives : {helper}.profile.ExecutionValid ({helper}.execute.value ({base}.helperPlacement.memory.project sourceValue))\n'
        f'      ({base}.helperPlacement.memory.project sourceValue))\n'
        f'    (counts : Fin {table}.multiplicityColumns.length → Source.BaseField)\n'
        f'    (row : Fin {model}.imported.data.length) (fallback : GKRAddress → Source.BaseField) :\n'
        '    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,\n'
        f'      (∀ wire, baseValue ({base}.inputBank.address wire) = {counter}.assigned ({helper}.canonical sourceValue) counts wire) ∧\n'
        f'      (∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (baseValue ∘ {base}.bank.address) = 0) ∧\n'
        f'      (∀ address, {graph}.isBase address = true → values address = hom (baseValue address)) ∧\n'
        f'      (∀ definition ∈ {graph}.definitions, definition.Holds hom challenges values) ∧\n'
        f'      (∀ gate ∈ {lookup}.gates, gate.Holds hom challenges gamma values) ∧\n'
        f'      (∀ gate ∈ {product}.gates, gate.Holds hom challenges values) ∧\n'
        f'      (∀ index, baseValue (GKRAddress.BaseLayerWitness ({table}.multiplicityColumns.get index)) = counts index) ∧\n'
        f'      (∀ column ∈ native.columns, baseValue column.address = {model}.value row column) ∧\n'
        f'      (∀ field ∈ {fields}.fields, (field.value ({fields}.sourceValues baseValue)).val < 524288) := by\n'
        f'  let initial := {helper}.canonical sourceValue\n'
        f'  let extended := {counter}.assigned initial counts\n'
        f'  have holds := {counter}.source_preserved initial counts ({helper}.source_holds sourceValue original clockValid)\n'
        f'  let full := {base}.artifact.translation.extend extended\n'
        f'  let baseValue := {base}.bank.materialize full ({model}.baseOracle row fallback)\n'
        f'  have arithmetic := {base}.full_arithmetic_extends extended holds\n'
        f'  have baseArithmetic := WireBank.materialize_gates {base}.bank {base}.bankRoundTrip full\n'
        f'    ({model}.baseOracle row fallback) {base}.artifact.gates arithmetic.2\n'
        f'  have inputAgreement (wire) : baseValue ({base}.inputBank.address wire) = extended wire :=\n'
        f'    WireBank.materialize_source_input {base}.bank {base}.inputBank {base}.artifact.projection\n'
        f'      {base}.inputCoordinates {base}.bankRoundTrip extended full arithmetic.1\n'
        f'      ({model}.baseOracle row fallback) wire\n'
        f'  refine ⟨baseValue, {graph}.canonical hom challenges gamma baseValue, inputAgreement, baseArithmetic,\n'
        f'    {graph}.canonical_base hom challenges gamma baseValue,\n'
        f'    {graph}.canonical_affines hom challenges gamma baseValue baseArithmetic,\n'
        f'    {graph}.canonical_lookups hom challenges gamma baseValue,\n'
        f'    {graph}.canonical_products hom challenges gamma baseValue, ?_,\n'
        f'    native.materialized_cells {model} row fallback full, ?_⟩\n'
        '  · intro index\n'
        f'    have actual := inputAgreement ({counter}.slots index)\n'
        f'    rw [{counter}.slotsRoundTrip index] at actual\n'
        f'    exact actual.trans ({counter}.counts_at initial counts index)\n'
        '  · intro field member\n'
        f'    have same := Source.HelperField.transport_value field {base}.helperPlacement {fields}.placement\n'
        f'      {base}.inputBank {memory}.bank (List.all_eq_true.mp {helper}.transportChecked field member)\n'
        '      extended baseValue inputAgreement\n'
        f'    change (field.value ({fields}.placement.project (baseValue ∘ {memory}.bank.address))).val < 524288\n'
        f'    rw [same, {counter}.helpers_preserved initial counts field member]\n'
        f'    exact {helper}.helper_membership sourceValue primitives field member\n\n'
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
                raise ValueError('lookup oracle frame changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                    cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
