#!/usr/bin/env python3
"""Bind all native Clean arguments before one complete numeric check."""
import argparse
import json
import re

from export_gkr_translations import LEAN
from gkr_packed_functional_steps import balanced
from gkr_packed_query_frame import capture_name, merge_slices
from gkr_packed_rotate_boundary import preflight

PILOT_CASES = ('WordMemoryCached', 'WordMemoryUncached')
CASES = PILOT_CASES + ('BlakeRoundCached', 'BlakeRoundUncached')


def metadata(case):
    name = capture_name(case)
    pair = json.loads((LEAN / f'artifacts/compiler/{name}.json').read_text())
    cert = json.loads((LEAN / f'artifacts/compiler/lookup/{name}.json').read_text())
    helper = (LEAN / f'Airbender/Proofs/GKRProtocol/HelperNative/{case}.lean').read_text()
    indices_text = json.loads(re.search(r'selectors ("(?:[^"\\]|\\.)*")', helper).group(1))
    return name, pair, cert, indices_text, json.loads(indices_text)


def model(case, family):
    return f'Airbender.Compiler.{family}.{case}.native'


def scalar_commands(case, phase):
    name, _, _, indices_text, _ = metadata(case)
    checks = f' phase {phase}' + (f' using_checks Airbender.Compiler.CleanArgumentChecks.{case}' if phase else '')
    source = (f'import_clean_lookup_arguments native from "artifacts/compiler/{name}.json"\n'
              f'  certificate "artifacts/compiler/lookup/{name}.json"\n')
    for key, family in [('clean_model', 'CleanArithmeticNative'), ('base_model', 'FullArithmeticNative'),
                        ('lookup_model', 'LookupNative'), ('query_model', 'LookupSourceNative'), ('links_model', 'FunctionalLinksNative')]:
        source += f'  {key} {model(case, family)}\n'
    source = source.rstrip() + checks + '\n\n'
    source += (f'import_clean_helper_arguments native from "artifacts/compiler/{name}.json"\n'
               f'  helper_indices {json.dumps(indices_text)}\n')
    for key, family in [('clean_model', 'CleanArithmeticNative'), ('base_model', 'FullArithmeticNative'),
                        ('helper_model', 'HelperNative'), ('memory_model', 'MemoryNative'), ('links_model', 'FunctionalLinksNative')]:
        source += f'  {key} {model(case, family)}\n'
    return source.rstrip() + checks + '\n'


def generic_command(case, phase):
    name, pair, _, _, _ = metadata(case)
    count = len(pair['circuit']['generic_lookups'])
    if not count:
        return ''
    source = (f'import_clean_generic_arguments native from "artifacts/compiler/{name}.json"\n'
              f'  certificate "artifacts/compiler/lookup/{name}.json"\n')
    for key, family in [('clean_model', 'CleanArithmeticNative'), ('base_model', 'FullArithmeticNative'),
                        ('lookup_model', 'LookupNative'), ('query_model', 'LookupSourceNative'), ('links_model', 'FunctionalLinksNative')]:
        source += f'  {key} {model(case, family)}\n'
    source += f'  start 0 stop {count} part_size 8 phase {phase}'
    if phase:
        source += f' using_checks Airbender.Compiler.CleanArgumentChecks.{case}'
    return source + '\n'


def generic_data(case):
    name, pair, cert, _, _ = metadata(case)
    queries = pair['circuit']['generic_lookups']
    if not queries:
        return ''
    rows = {row['native_index']: row for row in cert['rows'] if row['kind'] == 'generic'}
    if set(rows) != set(range(len(queries))):
        raise ValueError('generic query coverage changed: ' + name)
    lines, names = [], []
    for index, query in enumerate(queries):
        source_index = rows[index]['source_index']
        if len(query['columns']) != len(rows[index]['fields']):
            raise ValueError('generic query width changed: ' + name)
        stem = f'genericExpressions{index}'
        entries = ', '.join(f'part{index // 8}.genericExpression{source_index}_{column}'
                            for column in range(len(query['columns'])))
        lines.append(f'noncomputable def {stem} : Vector (_root_.Expression Source.BaseField) {len(query["columns"])} :=\n  #v[{entries}]\n')
        names.append(stem)
    width = pair['circuit']['generic_lookup_tables_width']
    lines.append(f'noncomputable def genericExpressions : List (Vector (_root_.Expression Source.BaseField) {width}) :=\n  [' + ', '.join(names) + ']\n')
    return '\n'.join(lines)


def native_wrapper(case, generic=False):
    family = 'CleanGenericArgumentsNative' if generic else 'CleanArgumentsNative'
    stem = 'Airbender.Proofs.GKRProtocol.CleanArgumentChecks.' + case
    namespace = 'Airbender.Compiler.' + family + '.' + case
    return (f'import {stem}.Certificate\n\nnamespace {namespace}\nopen Airbender Airbender.Compiler\n'
            'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 32768\n\n' +
            (generic_command(case, 1) if generic else scalar_commands(case, 1)) + '\nend ' + namespace + '\n')


def descriptors(case):
    _, pair, cert, _, indices = metadata(case)
    clean, base = model(case, 'CleanArithmeticNative'), model(case, 'FullArithmeticNative')
    lookup, query = model(case, 'LookupNative'), model(case, 'LookupSourceNative')
    helper, memory = model(case, 'HelperNative'), model(case, 'MemoryNative')
    args, generic = model(case, 'CleanArgumentsNative'), model(case, 'CleanGenericArgumentsNative')
    rows = []
    for row_index, row in enumerate(cert['rows']):
        if row['kind'] == 'range16':
            index = row['source_index']
            rows.append((f'rangeChecked{index}', f'{args}.rangeExpression{index}',
                         f'{lookup}.field{row_index}_0.lowered', f'{query}.bank'))
    operands = {item['source_index']: item for item in indices['operands']}
    if set(operands) != set(range(len(indices['operands']))):
        raise ValueError('helper operand coverage changed: ' + case)
    for index, operand in sorted(operands.items()):
        rows.append((f'timestampChecked{index}', f'{args}.timestampExpression{index}',
                     f'({helper}.recipe{operand["native_leaf"]}.expression {memory}.bank.placement)', f'{memory}.bank'))
    descriptions = {row['native_index']: (row_index, row) for row_index, row in enumerate(cert['rows']) if row['kind'] == 'generic'}
    if set(descriptions) != set(range(len(pair['circuit']['generic_lookups']))):
        raise ValueError('generic argument coverage changed: ' + case)
    for query_index, query_data in enumerate(pair['circuit']['generic_lookups']):
        row_index, description = descriptions[query_index]
        if len(query_data['columns']) != len(description['fields']):
            raise ValueError('generic argument width changed: ' + case)
        index = description['source_index']
        for column in range(len(description['fields'])):
            rows.append((f'genericChecked{index}_{column}', f'{generic}.part{query_index // 8}.genericExpression{index}_{column}',
                         f'{lookup}.field{row_index}_{column}.lowered', f'{query}.bank'))
    if len({row[0] for row in rows}) != len(rows):
        raise ValueError('argument theorem names collide: ' + case)
    return [(fact, f'NumericCleanArgumentChecks.ofNative {expression} {clean}.placement {base}.bank {native} {bank}',
             f'CleanExpression.nativeCheck {expression} {clean}.placement {base}.bank {native} {bank}')
            for fact, expression, native, bank in rows]


def modules(case):
    owner = 'Airbender.Compiler.CleanArgumentChecks.' + case
    stem = 'Airbender.Proofs.GKRProtocol.CleanArgumentChecks.' + case
    header = f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 8192\n\n'
    end = '\nend ' + owner + '\n'
    scalar_namespace = 'Airbender.Compiler.CleanArgumentsNative.' + case
    generic_namespace = 'Airbender.Compiler.CleanGenericArgumentsNative.' + case
    yield stem + '.Inputs', (
        'import Airbender.Import.GKRProtocol.CleanLookupArgumentsImport\n'
        'import Airbender.Import.GKRProtocol.CleanHelperArgumentsImport\n'
        'import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport\n'
        f'import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.{case}\n'
        f'import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.{case}\n\n'
        f'namespace {scalar_namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 32768\n\n' +
        scalar_commands(case, 0) + '\nend ' + scalar_namespace + '\n\n' +
        f'namespace {generic_namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 32768\n\n' + generic_command(case, 0) +
        '\nnamespace native\n\n' + generic_data(case) + '\nend native\n\nend ' + generic_namespace + '\n')
    rows = descriptors(case)
    yield stem + '.Typed', (f'import {stem}.Inputs\nimport Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks\n\n' +
        header + 'noncomputable def originalEntries := [\n  ' + ',\n  '.join(row[1] for row in rows) + ']\n' + end)
    lines, chunks = [], []
    for first in range(0, len(rows), 8):
        chunks.append('data' + str(first))
        lines.append(f'numeric_functional_base_capture data{first} := [\n  ' + ',\n  '.join(
            'NumericFunctionalBaseChecks.encode (' + row[1] + ')' for row in rows[first:first + 8]) + ']\n')
    lines.append('noncomputable def data : List NumericFunctionalBaseChecks.Data := ' + balanced(chunks) + '\n')
    yield stem + '.Data', (f'import {stem}.Typed\nimport Airbender.Import.GKRProtocol.NumericFunctionalBaseImport\n\n' + header + '\n'.join(lines) + end)
    lines, leaves = [], []
    stride = 1 if len(rows) >= 32 else 8
    for first in range(0, len(rows), stride):
        width = min(stride, len(rows) - first)
        block, offset = first // 8 * 8, first % 8
        view = f'(data{block}.drop {offset}).take {width}'
        leaf = f'binding{first}'
        lines.append(f'numeric_data_binding view{first} : (data.drop {first}).take {width} = {view}\n')
        lines.append(f'numeric_data_binding piece{first} : {view} = ((originalEntries.drop {first}).take {width}).map NumericFunctionalBaseChecks.encode\n')
        lines.append(f'theorem {leaf} : (data.drop {first}).take {width} = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop {first}).take {width} :=\n'
            f'  view{first}.trans (piece{first}.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode {first} {width}))\n')
        leaves.append((leaf, width))
    combined = merge_slices('source', 'data', '(originalEntries.map NumericFunctionalBaseChecks.encode)', 0, len(rows), leaves, lines)
    lines.append(f'theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=\n'
        f'  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) {len(rows)}\n'
        f'    (by decide +kernel) (by decide +kernel) {combined}\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header + '\n'.join(lines) + end)
    lines = ['private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩\n',
        'theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel\n',
        'theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=\n'
        '  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked\n']
    if len(rows) >= 32:
        for first in range(0, len(rows), 8):
            width = min(8, len(rows) - first)
            chunk = f'entries{first}'
            lines.append(f'noncomputable def {chunk} := [\n  ' + ',\n  '.join(row[1] for row in rows[first:first + width]) + ']\n')
            lines.append(f'theorem {chunk}_binding : ((originalEntries.drop {first}).take {width}) = {chunk} := by rfl\n')
            lines.append(f'theorem {chunk}_checked : {chunk}.all NumericFunctionalBaseChecks.Typed.check = true := by\n'
                f'  rw [← {chunk}_binding]\n'
                f'  exact NumericCleanArgumentChecks.checked_window originalChecked {first} {width}\n')
    for index, (fact, row, predicate) in enumerate(rows):
        source = f'entries{index // 8 * 8}' if len(rows) >= 32 else 'originalEntries'
        offset = index % 8 if len(rows) >= 32 else index
        checked = source + '_checked' if len(rows) >= 32 else 'originalChecked'
        lines.append(f'theorem {fact} : {predicate} = true := by\n'
            f'  have item : ({row}).check = true :=\n'
            f'    List.all_eq_true.mp {checked} ({source}.get ⟨{offset}, by decide +kernel⟩)\n'
            f'      (List.get_mem {source} ⟨{offset}, by decide +kernel⟩)\n'
            '  simpa only [NumericCleanArgumentChecks.ofNative_check] using item\n')
    yield stem + '.Certificate', (f'import {stem}.Bindings\n\n' + header + '\n'.join(lines) + end)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for case in args.case or CASES:
        generated = list(modules(case))
        if args.write:
            preflight(generated)
        for module, text in generated:
            path = LEAN / (module.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('Clean argument capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(module)


if __name__ == '__main__':
    main()
