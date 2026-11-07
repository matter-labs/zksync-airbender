#!/usr/bin/env python3
"""Bind actual lookup operands and derive their original checks from one result."""
import argparse
import json

from export_gkr_translations import LEAN
from gkr_lookup_source_certificate import synthesis
from gkr_packed_functional_steps import balanced
from gkr_packed_query_frame import capture_name, merge_slices
from gkr_packed_rotate_boundary import preflight
from gkr_wiring_instances import CASES as CIRCUITS

CASES = tuple(circuit + mode for circuit in CIRCUITS for mode in ('Cached',))


def metadata(case):
    name = capture_name(case)
    pair = json.loads((LEAN / f'artifacts/compiler/{name}.json').read_text())
    previous = json.loads((LEAN / f'artifacts/compiler/lookup/{name}.json').read_text())
    return name, previous, synthesis(pair, previous)


def command(case, phase, first=0, last=None):
    name, _, certificate = metadata(case)
    count = len(certificate['operands'])
    last = count if last is None else last
    if not 0 <= first <= last <= count:
        raise ValueError('source lookup input range is invalid: ' + case)
    if phase == 5 and (first != 0 or last != count):
        raise ValueError('source lookup checks require every operand: ' + case)
    selectors = json.dumps(json.dumps(certificate, separators=(',', ':')))
    checks = f' using_checks Airbender.Compiler.LookupSourceChecks.{case}' if phase == 5 else ''
    return (f'import_source_lookups native from "artifacts/compiler/{name}.json"\n'
            f'  certificate "artifacts/compiler/lookup/{name}.json"\n  selectors {selectors}\n'
            f'  reference Airbender.Compiler.LookupNative.{case}.native\n'
            f'  typing Airbender.Compiler.ConsumerNative.{case}.native.typing\n'
            f'  phase {phase} start {first} stop {last}{checks}\n')


def input_commands(case):
    count = len(metadata(case)[2]['operands'])
    # Data commands carry no per-field semantic proofs. Bound their elaboration
    # work while retaining one complete checker result for the capture.
    width = 32 if count > 128 else count
    commands = []
    for first in range(0, count, width):
        prefix = ''
        if case.startswith('BlakeRound') and first == 0:
            prefix = ('-- The complete affine source definitions exceed the default data import budget.\n'
                      'set_option maxHeartbeats 2000000 in\n')
        commands.append(prefix + command(case, 4, first, min(first + width, count)))
    return ''.join(commands)


def native_wrapper(case):
    namespace = 'Airbender.Compiler.LookupSourceNative.' + case
    return (f'import Airbender.Proofs.GKRProtocol.LookupSourceChecks.{case}.Certificate\n\n'
            f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
            'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 32768\n\n' +
            command(case, 5) + '\nend ' + namespace + '\n')


def descriptors(case):
    _, previous, certificate = metadata(case)
    native = 'Airbender.Compiler.LookupSourceNative.' + case + '.native'
    reference = 'Airbender.Compiler.LookupNative.' + case + '.native'
    typing = 'Airbender.Compiler.ConsumerNative.' + case + '.native.typing'
    arity = len(previous['addresses'])
    rows = []
    def flag(name, predicate):
        rows.append((name, f'NumericLookupSourceChecks.ofFlag (n := {arity}) ({predicate})', predicate))
    for operand in certificate['operands']:
        leaf = operand['native_leaf']
        flag(f'baseChecked{leaf}', f'{native}.encoding{leaf}.baseCheck {typing}')
        if operand['kind'] not in ['query', 'decoder']:
            continue
        for column in range(len(operand['fields'])):
            field = f'{native}.field{leaf}_{column}'
            recipe = f'{native}.recipe{leaf}_{column}'
            rows.append((f'fieldFacts{leaf}_{column}',
                f'NumericLookupSourceChecks.ofAgreement {field} {reference}.sourcePlacement {native}.bank',
                (f'{native}.bank.check {recipe}', f'{field}.check {reference}.sourcePlacement {native}.bank.placement',
                 f'inBank{leaf}_{column}', f'fieldChecked{leaf}_{column}')))
        if operand['kind'] == 'decoder':
            flag(f'maskBase{leaf}', f'{typing}.compatible (({native}.recipe{leaf}_0.inputs.headD (.BaseLayerWitness 0)), .base)')
    for group, description in certificate['groups'].items():
        if group == 'LookupTimestamps':
            continue
        stem = {'GenericLookup': 'generic', 'Lookup16Bits': 'range16'}[group]
        setups = [row for row in certificate['operands'] if row['group'] == group and row['kind'] == 'setup']
        if len(setups) != 1:
            raise ValueError('source setup coverage changed: ' + case)
        flag(stem + 'SetupChecked', f'{native}.leaf{setups[0]["native_leaf"]}.isSetup')
        flag(stem + 'SourceCoverage', f'decide ((({reference}.{stem}Tree).leaves.map {native}.{stem}Label).Perm (List.range ({native}.{stem}Queries.length + 1)))')
    if len({row[0] for row in rows}) != len(rows):
        raise ValueError('source check names collide: ' + case)
    return rows


def modules(case):
    owner = 'Airbender.Compiler.LookupSourceChecks.' + case
    stem = 'Airbender.Proofs.GKRProtocol.LookupSourceChecks.' + case
    native = 'Airbender.Compiler.LookupSourceNative.' + case
    header = (f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end = '\nend ' + owner + '\n'
    yield stem + '.Inputs', (f'import Airbender.Import.GKRProtocol.LookupSourceImport\n'
        f'import Airbender.Proofs.GKRProtocol.Native.{case}\nimport Airbender.Proofs.GKRProtocol.LookupNative.{case}\n\n'
        f'namespace {native}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\n'
        'set_option Elab.async false\nset_option maxRecDepth 32768\n\n' + input_commands(case) + '\nend ' + native + '\n')
    rows = descriptors(case)
    yield stem + '.Typed', (f'import {stem}.Inputs\nimport Airbender.Proofs.GKRProtocol.NumericLookupSourceChecks\n\n' +
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
    complete = merge_slices('source', 'data', '(originalEntries.map NumericFunctionalBaseChecks.encode)', 0, len(rows), leaves, lines)
    lines.append(f'theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=\n'
        f'  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) {len(rows)}\n'
        f'    (by decide +kernel) (by decide +kernel) {complete}\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header + '\n'.join(lines) + end)
    lines = ['private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩\n',
        'theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel\n',
        'theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=\n'
        '  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked\n']
    for first in range(0, len(rows), 8):
        width = min(8, len(rows) - first)
        lines.append(f'noncomputable def entries{first} := [\n  ' + ',\n  '.join(row[1] for row in rows[first:first + width]) + ']\n')
        lines.append(f'theorem entries{first}_binding : ((originalEntries.drop {first}).take {width}) = entries{first} := by rfl\n')
        lines.append(f'theorem entries{first}_checked : entries{first}.all NumericFunctionalBaseChecks.Typed.check = true := by\n'
            f'  rw [← entries{first}_binding]\n  exact NumericCleanArgumentChecks.checked_window originalChecked {first} {width}\n')
    for index, (fact, row, predicate) in enumerate(rows):
        source, offset = f'entries{index // 8 * 8}', index % 8
        statement = predicate + ' = true' if isinstance(predicate, str) else predicate[0] + ' = true ∧ ' + predicate[1] + ' = true'
        lemma = 'ofFlag_check' if isinstance(predicate, str) else 'ofAgreement_check, Bool.and_eq_true'
        lines.append(f'theorem {fact} : {statement} := by\n'
            f'  have item : ({row}).check = true :=\n'
            f'    List.all_eq_true.mp {source}_checked ({source}.get ⟨{offset}, by decide +kernel⟩)\n'
            f'      (List.get_mem {source} ⟨{offset}, by decide +kernel⟩)\n'
            f'  simpa only [NumericLookupSourceChecks.{lemma}] using item\n')
        if not isinstance(predicate, str):
            for side, name in enumerate(predicate[2:], 1):
                lines.append(f'theorem {name} : {predicate[side - 1]} = true := {fact}.{side}\n')
    yield stem + '.Certificate', (f'import {stem}.Bindings\nimport Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks\n\n' + header + '\n'.join(lines) + end)


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
            if args.check and (not path.exists() or path.read_text() != source):raise ValueError('source lookup capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != source):
                path.parent.mkdir(parents=True, exist_ok=True);path.write_text(source)
            print(module)


if __name__ == '__main__':main()
