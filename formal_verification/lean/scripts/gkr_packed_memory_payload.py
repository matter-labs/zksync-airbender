#!/usr/bin/env python3
"""Bind complete native memory checks to the original payloads and witnesses."""
import argparse
import json
from export_gkr_translations import LEAN, FAMILIES
from gkr_wiring_instances import CASES as STEMS
from gkr_framed_witness_instances import address_term
from gkr_packed_functional_steps import balanced
from gkr_packed_worker_ports import merge
from gkr_packed_rotate_boundary import preflight
import gkr_memory_certificate as legacy

ALL_CASES = tuple(stem + mode for stem in STEMS for mode in ('Cached', 'Uncached'))
CASES = ALL_CASES


def capture_name(case):
    for family, stem in zip(FAMILIES, STEMS, strict=True):
        for mode in ('Cached', 'Uncached'):
            if case == stem + mode:
                return family + '-' + mode.lower()
    raise ValueError('unknown memory payload capture: ' + case)


def selectors(case):
    name = capture_name(case)
    root = LEAN / 'artifacts/compiler'
    return legacy.synthesis(json.loads((root / (name + '.json')).read_text()),
                            json.loads((root / (name + '-source.json')).read_text()))


def inputs(case):
    text = legacy.module(capture_name(case), case)[1].replace('set_option maxHeartbeats 4000000\n', '')
    if case.startswith('BlakeRound'):
        text = text.replace('import_source_memory native',
            '-- The complete source definition bank exceeds the default command budget.\n'
            'set_option maxHeartbeats 2000000 in\nimport_source_memory native')
    return text.replace('\n\nend Airbender.Compiler.MemoryNative.', ' phase 0\n\nend Airbender.Compiler.MemoryNative.')


def header(case):
    return (f'namespace Airbender.Compiler.MemoryPayloadChecks.{case}\n'
            'open Airbender Airbender.Compiler\nset_option warningAsError true\n'
            'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')


def references(case):
    return ('Airbender.Compiler.MemoryNative.' + case + '.native',
            'Airbender.Compiler.ConsumerNative.' + case + '.native.typing')


def entries(case):
    native, typing = references(case)
    yield ('projection',), f'NumericMemoryPayloadChecks.ofInputs {native}.bank {typing} {native}.projectionInputs'
    for leaf in selectors(case)['leaves']:
        index = leaf['native_leaf']
        expansion = '[' + ', '.join(str(i) for i in leaf['expansion']) + ']'
        yield ('expansion', index), (f'NumericLookupSourceChecks.ofFlag (n := 0) '
            f'((LookupPayload.expand {native}.definitions {expansion} {native}.leaf{index}).isSome)')
        yield ('ports', index), f'NumericMemoryPayloadChecks.ofInputs {native}.bank {typing} ({native}.raw{index}).inputs'
    for group, row in selectors(case)['groups'].items():
        for occurrence, (leaf, index) in enumerate(zip(row['native_leaves'], row['source_labels'], strict=True)):
            source_row = (f'((({native}.{group}Rows)[{index}]?).getD '
                          '(Source.MemoryRow.mk (.constant 0) .zero .zero .zero))')
            yield ('fingerprint', group, occurrence), (f'NumericNativePayloadChecks.ofMemory '
                f'{native}.{group}Certificate{occurrence} {source_row}\n'
                f'  {native}.sourcePlacement {native}.bank {native}.raw{leaf} {typing}')
        if row['mask'] is not None:
            address = address_term(row['mask']['address'])
            yield ('mask', group), (f'NumericMemoryPayloadChecks.ofField {native}.{group}MaskField '
                f'{native}.sourcePlacement {native}.bank {typing} [{address}]')


def projection_modules(case):
    native, typing = references(case)
    root = LEAN / 'artifacts/compiler'
    pair = json.loads((root / (capture_name(case) + '.json')).read_text())
    snapshot = json.loads((root / (capture_name(case) + '-source.json')).read_text())
    layout = pair['circuit']['memory_layout']
    size = 2 * (len(layout['ram_access_sets']) + 2 * len(layout['teardown_sets']))
    if snapshot['configuration']['inline_init_teardown_pairs'] > 0:
        size += 2
    original = native + '.projectionInputs'
    code = f'(NumericMemoryPayloadChecks.inputPortCode {native}.bank {typing})'
    reference = f'({original}.map {code})'
    stem = 'Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case
    end = '\nend Airbender.Compiler.MemoryPayloadChecks.' + case + '\n'
    lines, chunks = [], []
    for first in range(0, size, 8):
        amount = min(8, size - first)
        name = 'projectionChunk' + str(first)
        chunks.append(f'({name}.getD 0 ⟨[], [], []⟩).ports')
        lines.append(f'numeric_functional_base_capture {name} := [NumericFunctionalBaseChecks.encode\n'
            f'  (NumericMemoryPayloadChecks.ofInputs {native}.bank {typing} (({original}.drop {first}).take {amount}))]\n')
    lines.append('noncomputable def projectionData : NumericFunctionalBaseChecks.Data :=\n  ⟨' + balanced(chunks) + ', [], []⟩\n')
    yield stem + '.ProjectionData', (f'import {stem}.Inputs\n'
        'import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks\n'
        'import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport\n\n' + header(case) + '\n'.join(lines) + end)
    lines = [f'attribute [local irreducible] projectionData {original}\n']
    leaves = []
    for first in range(0, size, 2):
        amount = min(2, size - first)
        chunk, offset = first // 8 * 8, first % 8
        view = f'((projectionChunk{chunk}.getD 0 ⟨[], [], []⟩).ports.drop {offset}).take {amount}'
        lines += [f'numeric_data_binding projection{first}_view : (projectionData.ports.drop {first}).take {amount} = {view}\n',
                  f'numeric_data_binding projection{first}_source : {view} = (({original}.drop {first}).take {amount}).map {code}\n']
        name = f'projection{first}_binding'
        lines.append(f'theorem {name} : (projectionData.ports.drop {first}).take {amount} = ({reference}.drop {first}).take {amount} :=\n'
            f'  projection{first}_view.trans (projection{first}_source.trans (NumericQueryFrameChecks.map_window {original} {code} {first} {amount}))\n')
        leaves.append((name, amount))
    whole = merge('projection', 'projectionData.ports', reference, 0, leaves, lines)
    lines.append(f'theorem projection_ports_binding : projectionData.ports = {reference} :=\n'
        f'  NumericQueryFrameChecks.complete_binding projectionData.ports {reference} {size}\n'
        f'    (by decide +kernel) (by rw [List.length_map]; decide +kernel) {whole}\n')
    lines.append(f'theorem projection_source_binding : projectionData = NumericFunctionalBaseChecks.encode\n'
        f'    (NumericMemoryPayloadChecks.ofInputs {native}.bank {typing} {original}) := by\n'
        '  rw [NumericMemoryPayloadChecks.encode_inputs]\n'
        '  simpa only [projectionData] using congrArg (fun ports => NumericFunctionalBaseChecks.Data.mk ports [] []) projection_ports_binding\n')
    yield stem + '.ProjectionBindings', (f'import {stem}.ProjectionData\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n'
        'import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks\n\n' + header(case) + '\n'.join(lines) + end)


def modules(case):
    stem = 'Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case
    end = '\nend Airbender.Compiler.MemoryPayloadChecks.' + case + '\n'
    selected = list(entries(case))
    yield stem + '.Inputs', inputs(case)
    yield from projection_modules(case)
    yield stem + '.Typed', (f'import {stem}.Inputs\n'
        'import Airbender.Proofs.GKRProtocol.NumericMemoryPayloadChecks\n\n' + header(case) +
        'noncomputable def originalEntries : List NumericFunctionalBaseChecks.Data := [\n  ' +
        ',\n  '.join('NumericFunctionalBaseChecks.encode (' + source + ')' for _, source in selected) + ']\n' + end)
    lines, chunks = [], ['[projectionData]']
    for first in range(1, len(selected), 4):
        name = 'data' + str(first)
        chunks.append(name)
        lines.append(f'numeric_functional_base_capture {name} := [\n  ' +
            ',\n  '.join('NumericFunctionalBaseChecks.encode (' + source + ')' for _, source in selected[first:first + 4]) + ']\n')
    lines.append('noncomputable def data : List NumericFunctionalBaseChecks.Data := ' + balanced(chunks) + '\n')
    yield stem + '.Data', (f'import {stem}.Typed\nimport {stem}.ProjectionData\n'
        'import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport\n\n' + header(case) + '\n'.join(lines) + end)
    lines = ['attribute [local irreducible] originalEntries data\n']
    leaves = []
    for index, (_, source) in enumerate(selected):
        if index == 0:
            lines.append('numeric_data_binding row0_view : (data.drop 0).take 1 = [projectionData]\n')
            lines.append(f'theorem row0_source : [projectionData] = [NumericFunctionalBaseChecks.encode ({source})] :=\n'
                         '  congrArg List.singleton projection_source_binding\n')
        else:
            chunk, offset = (index - 1) // 4 * 4 + 1, (index - 1) % 4
            lines.append(f'numeric_data_binding row{index}_view : (data.drop {index}).take 1 = (data{chunk}.drop {offset}).take 1\n')
            lines.append(f'numeric_data_binding row{index}_source : (data{chunk}.drop {offset}).take 1 = [NumericFunctionalBaseChecks.encode ({source})]\n')
        lines.append(f'numeric_data_binding row{index}_entry : (originalEntries.drop {index}).take 1 = [NumericFunctionalBaseChecks.encode ({source})]\n')
        lines.append(f'theorem row{index}_binding : (data.drop {index}).take 1 = (originalEntries.drop {index}).take 1 :=\n'
            f'  row{index}_view.trans (row{index}_source.trans row{index}_entry.symm)\n')
        leaves.append((f'row{index}_binding', 1))
    whole = merge('entries', 'data', 'originalEntries', 0, leaves, lines)
    lines.append(f'theorem source_binding : data = originalEntries :=\n'
        f'  NumericQueryFrameChecks.complete_binding data originalEntries {len(selected)}\n'
        f'    (by decide +kernel) (by decide +kernel) {whole}\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport {stem}.ProjectionBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n'
        'import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks\n\n' + header(case) + '\n'.join(lines) + end)
    lines = ['theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel\n']
    native, typing = references(case)
    certificate = selectors(case)
    for index, (label, source) in enumerate(selected):
        prefix = (f'  have valid := NumericNativePayloadChecks.checked_at ({source}) data {index}\n'
                  f'    (row{index}_view.trans row{index}_source) checked\n')
        kind = label[0]
        if kind == 'projection':
            name = 'projection'
            goal = (f'{native}.bank.inputCheck {native}.projectionInputs = true ∧\n'
                    f'    {native}.projectionInputs.all (fun address => {typing}.compatible (address, .base)) = true')
            proof = '  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid\n  simpa only [Bool.and_eq_true] using valid\n'
        elif kind == 'expansion':
            leaf = label[1]
            expansion = '[' + ', '.join(str(i) for i in certificate['leaves'][leaf]['expansion']) + ']'
            name = f'expansion{leaf}'
            goal = f'(LookupPayload.expand {native}.definitions {expansion} {native}.leaf{leaf}).isSome = true'
            proof = '  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid\n'
        elif kind == 'ports':
            leaf = label[1]
            name = f'ports{leaf}'
            goal = (f'{native}.bank.inputCheck ({native}.raw{leaf}).inputs = true ∧\n'
                    f'    ({native}.raw{leaf}).inputs.all (fun address => {typing}.compatible (address, .base)) = true')
            proof = '  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid\n  simpa only [Bool.and_eq_true] using valid\n'
        elif kind == 'fingerprint':
            group, occurrence = label[1:]
            row = certificate['groups'][group]
            leaf, source_index = row['native_leaves'][occurrence], row['source_labels'][occurrence]
            name = f'{group}Fingerprint{occurrence}'
            goal = (f'{native}.{group}Certificate{occurrence}.check\n'
                    f'    ((({native}.{group}Rows)[{source_index}]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))\n'
                    f'    {native}.sourcePlacement {native}.bank {native}.raw{leaf} = true')
            proof = '  rw [NumericNativePayloadChecks.ofMemory_check] at valid\n  simp only [Bool.and_eq_true] at valid\n  exact valid.2\n'
        else:
            group = label[1]
            address = address_term(certificate['groups'][group]['mask']['address'])
            name = group + 'Mask'
            goal = (f'({native}.bank.inputCheck [{address}] = true ∧\n'
                    f'      {typing}.compatible ({address}, .base) = true) ∧\n'
                    f'    {native}.{group}MaskField.check {native}.sourcePlacement = true')
            proof = ('  rw [NumericMemoryPayloadChecks.ofField_check] at valid\n'
                     '  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid\n')
        lines.append(f'theorem {name} : {goal} := by\n' + prefix + proof)
    yield stem + '.Certificate', f'import {stem}.Bindings\n\n' + header(case) + '\n'.join(lines) + end


def native(case):
    text = legacy.module(capture_name(case), case)[1]
    text = text[text.index('namespace Airbender.Compiler.MemoryNative.'):]
    text = text.replace('set_option maxHeartbeats 4000000\n', '')
    text = text.replace('\n\nend Airbender.Compiler.MemoryNative.',
        ' phase 1 using_checks Airbender.Compiler.MemoryPayloadChecks.' + case + '\n\nend Airbender.Compiler.MemoryNative.')
    return ('Airbender.Proofs.GKRProtocol.MemoryNative.' + case,
        'import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.' + case + '.Certificate\n\n' + text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    for flag in ('write', 'check'):
        parser.add_argument('--' + flag, action='store_true')
    args = parser.parse_args()
    generated = [entry for case in args.case or CASES for entry in [*modules(case), native(case)]]
    if args.write:
        preflight(generated)
    for module, text in generated:
        path = LEAN / (module.replace('.', '/') + '.lean')
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        if args.check and (not path.exists() or path.read_text() != text):
            raise SystemExit('stale memory payload: ' + str(path))
    print('PASS complete memory payload captures:', len(args.case or CASES))


if __name__ == '__main__':
    main()
