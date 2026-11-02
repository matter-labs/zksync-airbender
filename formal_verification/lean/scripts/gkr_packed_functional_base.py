#!/usr/bin/env python3
"""Bind every original base port and residual before one complete check."""
import argparse
import json

from export_gkr_translations import LEAN
from gkr_packed_functional_steps import balanced
from gkr_packed_query_frame import capture_name, merge_slices
from gkr_packed_rotate_boundary import preflight
from gkr_wiring_instances import CASES as CIRCUIT_CASES

PILOT_CASES = ('AddSubCached', 'BlakeRoundCached')
CASES = PILOT_CASES + tuple(stem + mode for stem in CIRCUIT_CASES if stem not in ['AddSub', 'BlakeRound']
                          for mode in ['Cached'])


def base_bindings(case):
    from gkr_functional_instances import selectors
    return selectors(json.loads((LEAN / f'artifacts/compiler/{capture_name(case)}.json').read_text())['circuit'])['base']


def modules(case):
    bindings = base_bindings(case)
    count = len(bindings)
    native = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    owner = 'Airbender.Compiler.FunctionalBaseChecks.' + case
    stem = 'Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.' + case
    header = (f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end = '\nend ' + owner + '\n'
    rows = [f'NumericFunctionalBaseChecks.ofBase {native}.baseRecipe{index} {native}.baseOutput{index} '
            f'{base}.bank {native}.isBase {base}.gate{binding["gate"]}.inputResidual'
            for index, binding in enumerate(bindings)]
    yield stem + '.Typed', (f'import Airbender.Proofs.GKRProtocol.FunctionalNative.{case}Foundation\n'
        'import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks\n\n' + header +
        'noncomputable def originalEntries := [\n  ' + ',\n  '.join(rows) + ']\n' + end)

    lines, chunks = [], []
    for first in range(0, count, 8):
        chunks.append('data' + str(first))
        lines.append(f'numeric_functional_base_capture data{first} := [\n  ' + ',\n  '.join(
            'NumericFunctionalBaseChecks.encode (' + row + ')' for row in rows[first:first + 8]) + ']\n')
    lines.append('noncomputable def data : List NumericFunctionalBaseChecks.Data := ' + balanced(chunks) + '\n')
    yield stem + '.Data', (f'import {stem}.Typed\nimport Airbender.Import.GKRProtocol.NumericFunctionalBaseImport\n\n' +
                          header + '\n'.join(lines) + end)

    lines, leaves = [], []
    stride = 1 if count >= 32 else 8
    for first in range(0, count, stride):
        width = min(stride, count - first)
        block, offset = first // 8 * 8, first % 8
        view = f'(data{block}.drop {offset}).take {width}'
        leaf = f'binding{first}'
        lines.append(f'numeric_data_binding view{first} : (data.drop {first}).take {width} = {view}\n')
        lines.append(f'numeric_data_binding piece{first} : {view} = ((originalEntries.drop {first}).take {width}).map NumericFunctionalBaseChecks.encode\n')
        lines.append(f'theorem {leaf} : (data.drop {first}).take {width} = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop {first}).take {width} :=\n'
            f'  view{first}.trans (piece{first}.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode {first} {width}))\n')
        leaves.append((leaf, width))
    combined = merge_slices('source', 'data', '(originalEntries.map NumericFunctionalBaseChecks.encode)', 0, count, leaves, lines)
    lines.append(f'theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=\n'
        f'  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) {count}\n'
        f'    (by decide +kernel) (by decide +kernel) {combined}\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header + '\n'.join(lines) + end)

    lines = ['private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩\n',
        'theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel\n',
        'theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=\n'
        '  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked\n']
    for index, row in enumerate(rows):
        lines.append(f'theorem baseFacts{index} : {native}.basePorts{index} = true ∧ {native}.baseRelation{index} = true := by\n'
            f'  have item : ({row}).check = true :=\n'
            f'    List.all_eq_true.mp originalChecked (originalEntries.get ⟨{index}, by decide +kernel⟩) (List.get_mem originalEntries ⟨{index}, by decide +kernel⟩)\n'
            '  rw [NumericFunctionalBaseChecks.ofBase_check] at item\n'
            f'  simpa only [Bool.and_eq_true, {native}.basePorts{index}, {native}.baseRelation{index}] using item\n')
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
                raise ValueError('functional base capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(module)


if __name__ == '__main__':
    main()
