#!/usr/bin/env python3
"""Construct the same native graph and lookup witnesses with an external base frame."""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_oracle_frame_instances import module as oracle_module
from gkr_materialized_witness_instances import module as lookup_module


def module(name, case):
    _, oracle_text = oracle_module(name, case)
    _, lookup_text = lookup_module(name, case)
    prefix = 'Airbender.Compiler.'
    owners = {key: prefix + model + '.' + case + '.native' for key, model in [
        ('base', 'FullArithmeticNative'), ('helper', 'HelperValidityNative'),
        ('fields', 'HelperNative'), ('counter', 'CounterFrameNative'), ('table', 'TableNative'),
        ('graph', 'FunctionalNative'), ('memory', 'MemoryNative'), ('oracle', 'OracleFrameNative'),
        ('setup', 'MaterializedNative')]}
    o = owners
    model = o['setup'] + '.model'
    start = oracle_text.index('theorem oracle_graph_extends')
    end = oracle_text.index('    ∃ baseValue', start)
    header = oracle_text[start:end].replace('theorem oracle_graph_extends', 'theorem framed_graph_extends')
    assert lookup_text.count('  let assignment : TypedAssignment R') == 1
    derivation = lookup_text[lookup_text.index('  let assignment : TypedAssignment R'):
                             lookup_text.index('\nnoncomputable def outputPorts')]
    body = (f"  let initial := {o['helper']}.canonical sourceValue\n"
            f"  let extended := {o['counter']}.assigned initial counts\n"
            f"  have holds := {o['counter']}.source_preserved initial counts ({o['helper']}.source_holds sourceValue original clockValid)\n"
            f"  let full := {o['base']}.artifact.translation.extend extended\n"
            f"  let baseValue := {o['base']}.bank.materialize full ({model}.baseOracle row fallback)\n"
            f"  let values := {o['graph']}.canonical hom challenges gamma baseValue\n"
            f"  have sourceArithmetic := {o['base']}.full_arithmetic_extends extended holds\n"
            f"  have arithmetic := WireBank.materialize_gates {o['base']}.bank {o['base']}.bankRoundTrip full\n"
            f"    ({model}.baseOracle row fallback) {o['base']}.artifact.gates sourceArithmetic.2\n"
            f"  have inputAgreement (wire) : baseValue ({o['base']}.inputBank.address wire) = extended wire :=\n"
            f"    WireBank.materialize_source_input {o['base']}.bank {o['base']}.inputBank {o['base']}.artifact.projection\n"
            f"      {o['base']}.inputCoordinates {o['base']}.bankRoundTrip extended full sourceArithmetic.1\n"
            f"      ({model}.baseOracle row fallback) wire\n"
            '  have externalAgreement (address) (outside) :\n'
            f"      baseValue address = {model}.baseOracle row fallback address :=\n"
            f"    WireBank.materialize_external {o['base']}.bank full ({model}.baseOracle row fallback) address outside\n"
            f"  have baseLaw := {o['graph']}.canonical_base hom challenges gamma baseValue\n"
            f"  have affine := {o['graph']}.canonical_affines hom challenges gamma baseValue arithmetic\n"
            f"  have lookups := {o['graph']}.canonical_lookups hom challenges gamma baseValue\n"
            f"  have products := {o['graph']}.canonical_products hom challenges gamma baseValue\n"
            f"  have countsAt (index) : baseValue (GKRAddress.BaseLayerWitness ({o['table']}.multiplicityColumns.get index)) = counts index := by\n"
            f"    have actual := inputAgreement ({o['counter']}.slots index)\n"
            f"    rw [{o['counter']}.slotsRoundTrip index] at actual\n"
            f"    exact actual.trans ({o['counter']}.counts_at initial counts index)\n"
            f"  have setupAt := {o['oracle']}.materialized_cells {model} row fallback full\n"
            f"  have helpers : ∀ field ∈ {o['fields']}.fields, (field.value ({o['fields']}.sourceValues baseValue)).val < 524288 := by\n"
            '    intro field member\n'
            f"    have same := Source.HelperField.transport_value field {o['base']}.helperPlacement {o['fields']}.placement\n"
            f"      {o['base']}.inputBank {o['memory']}.bank (List.all_eq_true.mp {o['helper']}.transportChecked field member)\n"
            '      extended baseValue inputAgreement\n'
            f"    change (field.value ({o['fields']}.placement.project (baseValue ∘ {o['memory']}.bank.address))).val < 524288\n"
            f"    rw [same, {o['counter']}.helpers_preserved initial counts field member]\n"
            f"    exact {o['helper']}.helper_membership sourceValue primitives field member\n"
            '  have outputs : OutputsPreserved hom challenges gamma sourceValue counts row values := by\n' +
            ''.join('  ' + line + '\n' for line in derivation.splitlines()) +
            '  refine ⟨baseValue, values, ?_, externalAgreement⟩\n'
            '  exact ⟨inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers, outputs⟩\n')
    target = 'GKRProtocol.FramedWitnessNative.' + case
    namespace = 'Airbender.Compiler.FramedWitnessNative.' + case
    content = (f'import GKRProtocol.MaterializedWitnessNative.{case}\nimport GKRProtocol.MemoryExecuteNative.{case}\n\n'
               f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
               f'open Airbender.Compiler.MaterializedWitnessNative.{case}\n'
               'set_option warningAsError true\nset_option Elab.async false\n'
               'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n' + header +
               '    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,\n'
               '      RowWitness hom challenges gamma sourceValue counts row baseValue values ∧\n'
               f"      ∀ address, addressEqual ({o['base']}.bank.address ({o['base']}.bank.placement address)) address = false →\n"
               f'        baseValue address = {model}.baseOracle row fallback address := by\n' + body +
               memory_layer(name, case, o, model, header, lookup_text) +
               f'\nend {namespace}\n')
    return target, content


def address_term(address):
    kind, data = next(iter(address.items()))
    if kind == 'InnerLayer':
        return f'(GKRAddress.InnerLayer {data["layer"]} {data["offset"]})'
    if kind in ['BaseLayerWitness', 'BaseLayerMemory']:
        return '(GKRAddress.' + kind + ' ' + str(data) + ')'
    raise ValueError('unsupported actual native product output address: ' + kind)


def memory_layer(name, case, o, model, header, lookup_text):
    frame = 'Airbender.Compiler.MemoryFrameNative.' + case + '.native'
    execute = 'Airbender.Compiler.MemoryExecuteNative.' + case + '.native'
    links = 'Airbender.Compiler.FunctionalLinksNative.' + case + '.native'
    typing = 'Airbender.Compiler.ConsumerNative.' + case + '.native.typing'
    pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
    groups = []
    for kind, ports in pair['circuit']['global_output_map'].items():
        stem = {'PermutationProduct': 'memory', 'InitsAndTeardownsProduct': 'initialization'}.get(kind)
        if stem:
            groups += [(stem + direction, address_term(port)) for direction, port in zip(['Read', 'Write'], ports, strict=True)]
    source_binder = header[header.index('    (sourceValue :'):header.index('    (original :')].strip()
    count_binder = f"(counts : Fin {o['table']}.multiplicityColumns.length → Source.BaseField)"
    baseline = frame + '.sourceMemoryValues sourceValue fallback'
    properties = []
    for stem, port in groups:
        effect = f"({o['memory']}.{stem}Rows.map (fun entry => entry.fingerprint ({baseline}) hom challenges)).prod"
        if stem.startswith('memory'):
            effect = f"maskProduct (hom ({o['memory']}.sourceExecute.value ({baseline}))) ({effect})"
        properties.append(f'values {port} = {effect}')
    out = ('\ndef MemoryOutputsPreserved {R : Type} [CommRing R]\n'
           '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
           f'    {source_binder}\n    (fallback : GKRAddress → Source.BaseField) (values : GKRAddress → R) : Prop :=\n  ' +
           '\n  ∧ '.join(properties) + '\n\n')
    out += ('theorem memory_outputs_preserved {R : Type} [CommRing R]\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            f'    {source_binder}\n    {count_binder}\n'
            f'    (row : Fin {model}.imported.data.length) (fallback : GKRAddress → Source.BaseField)\n'
            '    (baseValue : GKRAddress → Source.BaseField) (values : GKRAddress → R)\n'
            '    (witness : RowWitness hom challenges gamma sourceValue counts row baseValue values)\n'
            f"    (externalAgreement : ∀ address, addressEqual ({o['base']}.bank.address ({o['base']}.bank.placement address)) address = false →\n"
            f'      baseValue address = {model}.baseOracle row fallback address) :\n'
            '    MemoryOutputsPreserved hom challenges sourceValue fallback values := by\n'
            '  rcases witness with ⟨inputAgreement, arithmetic, baseLaw, affine, _, products, _, _, _, _⟩\n'
            '  let assignment : TypedAssignment R := ⟨baseValue, values⟩\n'
            f'  have typedEq : assignment.value {typing} hom = values := TypedAssignment.value_eq assignment {typing} hom baseLaw\n'
            f"  have defined : ∀ definition ∈ {o['memory']}.definitions, definition.Holds hom challenges (assignment.value {typing} hom) := by\n"
            f'    rw [typedEq, ← {links}.memoryDefinitionsAgree]\n    exact affine\n'
            '  have holds := products\n'
            f'  rw [← typedEq] at holds\n'
            '  unfold MemoryOutputsPreserved\n'
            '  refine ⟨' + ', '.join('?_ ' for _ in groups[:-1]) + ', ?_⟩\n')
    for stem, port in groups:
        out += f"  · have reduced := {o['memory']}.{stem}SourceReduction hom challenges assignment defined\n      ({links}.memoryCopies baseValue arithmetic) holds\n    rw [typedEq] at reduced\n"
        out += '    apply reduced.trans\n'
        native_effect = f"({o['memory']}.{stem}Rows.map (fun entry => entry.fingerprint ({o['memory']}.sourceValues baseValue) hom challenges)).prod"
        source_effect = f"({o['memory']}.{stem}Rows.map (fun entry => entry.fingerprint ({baseline}) hom challenges)).prod"
        if stem.startswith('memory'):
            out += f"    change maskProduct (hom ({o['memory']}.sourceExecute.value ({o['memory']}.sourceValues baseValue))) ({native_effect}) = _\n"
            out += f"    have executeSame := {frame}.execute_fields_preserved {model} row sourceValue counts fallback baseValue\n      inputAgreement externalAgreement {o['memory']}.sourceExecute (by simp [{frame}.executeFields])\n"
            out += '    rw [executeSame]\n'
            out += f"    by_cases inactive : {o['memory']}.sourceExecute.value ({baseline}) = 0\n"
            out += '    · simp only [inactive, map_zero, maskProduct_inactive]\n'
            out += f"    · have active : {o['helper']}.execute.value ({o['base']}.helperPlacement.memory.project sourceValue) ≠ 0 := by\n        rw [← {execute}.execute_source sourceValue fallback]\n        exact inactive\n"
            indent = '      '
            out += f"      apply congrArg (maskProduct (hom ({o['memory']}.sourceExecute.value ({baseline}))))\n"
        else:
            out += f'    change {native_effect} = {source_effect}\n'
            indent = '    '
        out += indent + 'apply congrArg List.prod\n' + indent + 'apply List.map_congr_left\n' + indent + 'intro entry member\n'
        out += indent + 'apply Source.MemoryRow.fingerprint_congr\n' + indent + 'intro field included\n'
        if stem.startswith('memory'):
            out += indent + f'apply {frame}.ram_fields_preserved {model} row sourceValue counts fallback baseValue inputAgreement externalAgreement active field\n'
            frame_fields = 'ramFields'
            left_rows = o['memory'] + '.memoryReadRows'
            right_rows = o['memory'] + '.memoryWriteRows'
        else:
            out += indent + f'apply {frame}.initialization_fields_preserved {model} row sourceValue counts fallback baseValue inputAgreement externalAgreement field\n'
            frame_fields = 'initializationFields'
            left_rows = o['memory'] + '.initializationReadRows'
            right_rows = o['memory'] + '.initializationWriteRows'
        out += indent + f'change field ∈ ({left_rows} ++ {right_rows}).flatMap Source.MemoryRow.fields\n'
        side = 'left' if stem.endswith('Read') else 'right'
        out += indent + f'exact List.mem_flatMap.mpr ⟨entry, List.mem_append_{side} _ member, included⟩\n'
    out += ('\n' + header.replace('theorem framed_graph_extends', 'theorem complete_row_extends') +
            '    ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,\n'
            '      RowWitness hom challenges gamma sourceValue counts row baseValue values ∧\n'
            f"      (∀ address, addressEqual ({o['base']}.bank.address ({o['base']}.bank.placement address)) address = false →\n"
            f'        baseValue address = {model}.baseOracle row fallback address) ∧\n'
            '      MemoryOutputsPreserved hom challenges sourceValue fallback values := by\n'
            '  obtain ⟨baseValue, values, witness, externalAgreement⟩ :=\n'
            '    framed_graph_extends hom challenges gamma sourceValue original clockValid primitives counts row fallback\n'
            '  exact ⟨baseValue, values, witness, externalAgreement,\n'
            '    memory_outputs_preserved hom challenges gamma sourceValue counts row fallback baseValue values witness externalAgreement⟩\n')
    out += ('\ndef CompleteRowWitness {R : Type} [CommRing R]\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            f'    {source_binder}\n    {count_binder}\n'
            f'    (row : Fin {model}.imported.data.length) (fallback : GKRAddress → Source.BaseField)\n'
            '    (baseValue : GKRAddress → Source.BaseField) (values : GKRAddress → R) : Prop :=\n'
            '  RowWitness hom challenges gamma sourceValue counts row baseValue values ∧\n'
            f"  (∀ address, addressEqual ({o['base']}.bank.address ({o['base']}.bank.placement address)) address = false →\n"
            f'    baseValue address = {model}.baseOracle row fallback address) ∧\n'
            '  MemoryOutputsPreserved hom challenges sourceValue fallback values\n\n')
    start = lookup_text.index('theorem native_lookup_trace_extends')
    global_trace = lookup_text[start:lookup_text.rindex('\nend Airbender.Compiler.MaterializedWitnessNative.')]
    global_trace = global_trace.replace('theorem native_lookup_trace_extends', 'theorem complete_trace_extends')
    global_trace = global_trace.replace('RowWitness hom challenges gamma (sourceValue row) (counts row) row (baseValue row) (values row)',
        'CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) (baseValue row) (values row)')
    global_trace = global_trace.replace('RowWitness hom challenges gamma (sourceValue row) (counts row) row baseValue values',
        'CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row (fallback row) baseValue values')
    global_trace = global_trace.replace('source_outputs_extends hom', 'complete_row_extends hom')
    global_trace = global_trace.replace('(correct row).2.2.2.2.2.2.2.2.2 group', '(correct row).1.2.2.2.2.2.2.2.2.2 group')
    out += global_trace + '\n'
    trace_binder = source_binder.replace('(sourceValue : ', f'(sourceValue : Fin {model}.imported.data.length → ')
    trace_properties = []
    for stem, port in groups:
        before = f'{frame}.sourceMemoryValues (sourceValue row) (fallback row)'
        source_effect = f"({o['memory']}.{stem}Rows.map (fun entry => entry.fingerprint ({before}) hom challenges)).prod"
        if stem.startswith('memory'):
            source_effect = f"maskProduct (hom ({o['memory']}.sourceExecute.value ({before}))) ({source_effect})"
        trace_properties.append(f"((List.finRange {model}.imported.data.length).map (fun row => values row {port})).prod =\n    ((List.finRange {model}.imported.data.length).map (fun row => {source_effect})).prod")
    out += ('theorem memory_trace_products_preserved {R : Type} [CommRing R]\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            f'    {trace_binder}\n'
            f"    (counts : Fin {model}.imported.data.length → Fin {o['table']}.multiplicityColumns.length → Source.BaseField)\n"
            f'    (fallback : Fin {model}.imported.data.length → GKRAddress → Source.BaseField)\n'
            f'    (baseValue : Fin {model}.imported.data.length → GKRAddress → Source.BaseField)\n'
            f'    (values : Fin {model}.imported.data.length → GKRAddress → R)\n'
            '    (witnesses : ∀ row, CompleteRowWitness hom challenges gamma (sourceValue row) (counts row) row\n'
            '      (fallback row) (baseValue row) (values row)) :\n  ' + '\n  ∧ '.join(trace_properties) + ' := by\n' +
            '  refine ⟨' + ', '.join('?_ ' for _ in groups[:-1]) + ', ?_⟩\n')
    for index, _ in enumerate(groups):
        projection = '(witnesses row).2.2' + '.2' * index + ('.1' if index < len(groups) - 1 else '')
        out += ('  · apply congrArg List.prod\n    apply List.map_congr_left\n    intro row _\n    exact ' + projection + '\n')
    return out


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
                raise ValueError('framed native graph witness changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                               cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
