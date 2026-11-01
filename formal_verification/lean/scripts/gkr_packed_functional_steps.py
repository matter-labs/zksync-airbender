#!/usr/bin/env python3
"""Bind complete literal ports and check the original functional program."""
import argparse
import hashlib
import json

from export_gkr_translations import LEAN
from gkr_packed_query_frame import capture_name, merge_slices
from gkr_packed_rotate_boundary import preflight

CASES = ('BlakeRoundCached', 'BlakeRoundUncached')
DATA = LEAN / 'artifacts/compiler/numeric-functional-steps'


def source_paths(case):
    return [f'artifacts/compiler/{capture_name(case)}.json',
            f'Airbender/Proofs/GKRProtocol/FunctionalNative/{case}Foundation.lean',
            'Airbender/Import/GKRProtocol/FunctionalImport.lean',
            'Airbender/Proofs/GKRProtocol/Functional.lean',
            'Airbender/Proofs/GKRProtocol/NumericFunctionalStepChecks.lean',
            'Airbender/Import/GKRProtocol/NumericFunctionalStepImport.lean',
            'scripts/ExportFunctionalPorts.lean']


def digest(path):
    return hashlib.sha256((LEAN / path).read_bytes()).hexdigest()


def capture(case):
    from gkr_functional_instances import selectors
    value = json.loads((DATA / (capture_name(case) + '.json')).read_text())
    if set(value) != {'format', 'sources', 'ports'} or value['format'] != 1:
        raise ValueError('invalid functional port capture')
    expected = {path: digest(path) for path in source_paths(case)}
    if value['sources'] != expected:
        raise ValueError('functional port source hashes changed: ' + case)
    rows = value['ports']
    count = selectors(json.loads((LEAN / source_paths(case)[0]).read_text())['circuit'])['steps']
    if not isinstance(rows, list) or len(rows) != count:
        raise ValueError('incomplete functional port capture: ' + case)
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'outputs', 'inputs'}:
            raise ValueError('invalid functional port row')
        for ports in row.values():
            if not isinstance(ports, list) or any(
                    not isinstance(pair, list) or len(pair) != 2 or
                    any(type(item) is not int or item < 0 for item in pair) or pair[1] > 1
                    for pair in ports):
                raise ValueError('invalid natural port or base flag')
    return rows


def balanced(items):
    if len(items) == 1:
        return items[0]
    middle = len(items) // 2
    return '(' + balanced(items[:middle]) + ' ++ ' + balanced(items[middle:]) + ')'


def modules(case):
    rows = capture(case)
    count = len(rows)
    native = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    stem = 'Airbender.Proofs.GKRProtocol.FunctionalStepChecks.' + case
    owner = 'Airbender.Compiler.FunctionalStepChecks.' + case
    header = (f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end = '\nend ' + owner + '\n'
    def pairs(values):
        return '[' + ', '.join(f'({code}, {flag})' for code, flag in values) + ']'
    chunks, lines = [], []
    for first in range(0, count, 32):
        chunks.append('ports' + str(first))
        values = ',\n  '.join('⟨[], ' + pairs(row['outputs']) + ', ' + pairs(row['inputs']) + '⟩'
                              for row in rows[first:first + 32])
        lines.append(f'noncomputable def ports{first} : List NumericFunctionalStepChecks.Data := [\n  {values}]\n')
    lines.append('noncomputable def ports : List NumericFunctionalStepChecks.Data := ' + balanced(chunks) + '\n')
    yield stem + '.Data', ('import Airbender.Proofs.GKRProtocol.NumericFunctionalStepChecks\n\n' +
                          header + '\n'.join(lines) + end)

    lines = [f'noncomputable def encodePort (step : FunctionalStep) := NumericFunctionalStepChecks.encode {native}.isBase ([], step)\n',
             f'noncomputable def sourcePorts := {native}.program.map encodePort\n']
    leaves = []
    for first in range(0, count, 8):
        width = min(8, count - first)
        base, offset = first // 32 * 32, first % 32
        view = f'(ports{base}.drop {offset}).take {width}'
        leaf = f'portsSlice{first}'
        lines.append(f'numeric_data_binding portsView{first} : (ports.drop {first}).take {width} = {view}\n')
        lines.append(f'numeric_data_binding portsPiece{first} : {view} = (({native}.program.drop {first}).take {width}).map encodePort\n')
        lines.append(f'theorem {leaf} : (ports.drop {first}).take {width} = (sourcePorts.drop {first}).take {width} :=\n'
                     f'  portsView{first}.trans (portsPiece{first}.trans (NumericQueryFrameChecks.map_window {native}.program encodePort {first} {width}))\n')
        leaves.append((leaf, width))
    combined = merge_slices('ports', 'ports', 'sourcePorts', 0, count, leaves, lines)
    lines.append(f'theorem programLength : {native}.program.length = {count} := by decide +kernel\n')
    lines.append(f'theorem ports_binding : ports = sourcePorts :=\n'
                 f'  NumericQueryFrameChecks.complete_binding ports sourcePorts {count}\n'
                 f'    (by decide +kernel) (by rw [sourcePorts, List.length_map, programLength]) {combined}\n')
    yield stem + '.Bindings', (f'import {stem}.Data\n'
        f'import Airbender.Proofs.GKRProtocol.FunctionalNative.{case}Foundation\n'
        'import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header + '\n'.join(lines) + end)

    yield stem + '.Certificate', (f'import {stem}.Bindings\n\n' + header +
        'theorem checked : NumericFunctionalStepChecks.treeCheck ∅ ports = true := by decide +kernel\n\n'
        f'theorem programChecked : FunctionalProgram.check {native}.isBase [] {native}.program = true :=\n'
        f'  NumericFunctionalStepChecks.tree_check_sound {native}.isBase {native}.program ports ports_binding checked\n\n'
        f'noncomputable def entries := NumericFunctionalStepChecks.sourceEntries [] {native}.program\n\n'
        f'theorem entriesChecked : entries.all (fun entry => entry.2.check {native}.isBase entry.1) = true :=\n'
        f'  (NumericFunctionalStepChecks.sourceEntries_check {native}.isBase [] {native}.program).trans programChecked\n\n'
        f'theorem entriesLength : entries.length = {count} := by\n'
        '  rw [entries, NumericFunctionalStepChecks.sourceEntries_length, programLength]\n' + end)

    lines = []
    for index in range(count):
        lines.append(f'theorem stepChecked{index} : step{index}.check isBase known{index} = true := by\n'
                     f'  have inside : {index} < {owner}.entries.length := by\n'
                     f'    rw [{owner}.entriesLength]; decide +kernel\n'
                     f'  exact List.all_eq_true.mp {owner}.entriesChecked\n'
                     f'    ({owner}.entries.get ⟨{index}, inside⟩) (List.get_mem {owner}.entries ⟨{index}, inside⟩)\n')
    yield stem + '.Corollaries', (f'import {stem}.Certificate\n\nnamespace {native}\n'
        'open Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 8192\n\n' + '\n'.join(lines) + '\nend ' + native + '\n')


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
                raise ValueError('functional step capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(module)


if __name__ == '__main__':
    main()
