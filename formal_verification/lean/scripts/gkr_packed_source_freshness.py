#!/usr/bin/env python3
"""Bind native source addresses and check every multiplicity address together."""
import argparse
import json
from export_gkr_translations import LEAN
from gkr_packed_functional_steps import balanced
from gkr_packed_query_frame import capture_name, merge_slices
from gkr_packed_rotate_boundary import preflight

CASES = ('BlakeRoundCached', 'BlakeRoundUncached')


def table_wrapper(case, source):
    source = source.replace(f'import Airbender.Proofs.GKRProtocol.LookupSourceNative.{case}\n',
        f'import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.{case}.Certificate\n')
    source = source.replace('set_option maxHeartbeats 4000000\n', '')
    return source.replace(f'  roles Airbender.Compiler.ConsumerNative.{case}.native.typing\n',
        f'  roles Airbender.Compiler.ConsumerNative.{case}.native.typing\n'
        f'  using_freshness Airbender.Compiler.SourceFreshnessChecks.{case}\n')


def metadata(case):
    pair = json.loads((LEAN / f'artifacts/compiler/{capture_name(case)}.json').read_text())
    keys = {'GenericLookup': ('generic', 'generic_lookup'),
            'Lookup16Bits': ('range16', 'range_check_16'),
            'LookupTimestamps': ('timestamp', 'timestamp_range_check')}
    targets = []
    for kind in pair['circuit']['global_output_map']:
        if kind in keys:
            stem, field = keys[kind]
            span = pair['circuit']['witness_layout']['multiplicities_columns_for_' + field]
            if span['end'] != span['start'] + 1:
                raise ValueError('multiplicity span changed: ' + case)
            targets.append((stem, span['start']))
    return pair['source']['num_variables'], targets


def modules(case):
    count, targets = metadata(case)
    owner = 'Airbender.Compiler.SourceFreshnessChecks.' + case
    stem = 'Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.' + case
    bank = 'Airbender.Compiler.LookupSourceNative.' + case + '.native.bank'
    placement = 'Airbender.Compiler.LookupNative.' + case + '.native.sourcePlacement'
    address = lambda index: f'{bank}.address ({placement} {index})'
    encode = lambda value: 'NumericFunctionalBaseChecks.encode (NumericSourceFreshnessChecks.ofAddress (' + value + '))'
    header = (f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end = '\nend ' + owner + '\n'
    yield stem + '.Typed', (f'import Airbender.Proofs.GKRProtocol.LookupSourceNative.{case}\n'
        'import Airbender.Proofs.GKRProtocol.NumericSourceFreshnessChecks\n\n' + header +
        f'noncomputable def sourceAddresses := (List.range {count}).map (fun index => {address("index")})\n'
        'def targetAddresses : List GKRAddress := [' + ', '.join('.BaseLayerWitness ' + str(column) for _, column in targets) + ']\n'
        'noncomputable def originalEntries := sourceAddresses.map NumericSourceFreshnessChecks.ofAddress\n' + end)
    lines, chunks = [], []
    for first in range(0, count, 8):
        chunks.append('data' + str(first))
        lines.append(f'numeric_functional_base_capture data{first} := [\n  ' + ',\n  '.join(
            encode(address(index)) for index in range(first, min(first + 8, count))) + ']\n')
    lines.append('noncomputable def data : List NumericFunctionalBaseChecks.Data := ' + balanced(chunks) + '\n')
    lines.append('numeric_functional_base_capture targetData := [' + ', '.join(encode('.BaseLayerWitness ' + str(column)) for _, column in targets) + ']\n')
    yield stem + '.Data', (f'import {stem}.Typed\nimport Airbender.Import.GKRProtocol.NumericFunctionalBaseImport\n\n' + header + '\n'.join(lines) + end)
    lines, leaves = [], []
    for first in range(0, count, 8):
        width = min(8, count - first)
        lines.append(f'numeric_data_binding view{first} : (data.drop {first}).take {width} = data{first}\n')
        lines.append(f'numeric_data_binding piece{first} : data{first} = ((originalEntries.drop {first}).take {width}).map NumericFunctionalBaseChecks.encode\n')
        lines.append(f'theorem binding{first} : (data.drop {first}).take {width} = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop {first}).take {width} :=\n'
            f'  view{first}.trans (piece{first}.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode {first} {width}))\n')
        leaves.append(('binding' + str(first), width))
    full = merge_slices('source', 'data', '(originalEntries.map NumericFunctionalBaseChecks.encode)', 0, count, leaves, lines)
    lines.append(f'theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=\n'
        f'  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) {count}\n'
        f'    (by decide +kernel) (by decide +kernel) {full}\n')
    lines.append('theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by\n'
        '  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding\n')
    lines.append('numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header + '\n'.join(lines) + end)
    lines = ['theorem checked : NumericSourceFreshnessChecks.check data targetData = true := by decide +kernel\n',
        'theorem originalChecked : targetAddresses.all (fun target => sourceAddresses.all (fun address => !addressEqual address target)) = true :=\n'
        '  NumericSourceFreshnessChecks.check_sound sourceAddresses targetAddresses data targetData source_binding target_binding checked\n']
    for index, (name, column) in enumerate(targets):
        lines.append(f'theorem {name}Fresh : (List.range {count}).all (fun index => !addressEqual ({address("index")}) (.BaseLayerWitness {column})) = true := by\n'
            '  have item := List.all_eq_true.mp originalChecked\n'
            f'    (targetAddresses.get ⟨{index}, by decide +kernel⟩) (List.get_mem targetAddresses ⟨{index}, by decide +kernel⟩)\n'
            f'  have target : targetAddresses.get ⟨{index}, by decide +kernel⟩ = .BaseLayerWitness {column} := by rfl\n'
            '  rw [target] at item\n'
            '  simpa only [sourceAddresses, List.all_map, Function.comp_def] using item\n')
    yield stem + '.Certificate', (f'import {stem}.Bindings\n\n' + header + '\n'.join(lines) + end)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for case in args.case or CASES:
        generated = list(modules(case))
        if args.write:preflight(generated)
        for module, source in generated:
            path = LEAN / (module.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != source):raise ValueError('source freshness capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != source):
                path.parent.mkdir(parents=True, exist_ok=True);path.write_text(source)
            print(module)


if __name__ == '__main__':main()
