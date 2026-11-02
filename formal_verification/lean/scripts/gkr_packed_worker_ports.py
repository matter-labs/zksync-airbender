#!/usr/bin/env python3
"""Bind all native worker addresses and history bounds to one kernel result."""
import argparse
import hashlib
import json
import re
from export_gkr_translations import LEAN
import gkr_worker_ports_instances as legacy
from gkr_packed_functional_steps import balanced
from gkr_packed_rotate_boundary import preflight

CASES = tuple(stem + mode for stem, _, _ in legacy.FAMILIES.values() for mode in ('Cached', 'Uncached'))
DIMENSIONS = LEAN / 'artifacts/checkers/worker-port-dimensions.json'


def identity(case):
    for family, (stem, model, _) in legacy.FAMILIES.items():
        if case in (stem + 'Cached', stem + 'Uncached'):
            return family, case[len(stem):].lower(), model
    raise ValueError('unknown worker capture: ' + case)


def fingerprint(case):
    family, mode, _ = identity(case)
    paths = [LEAN / f'artifacts/compiler/{family}-{mode}.json',
             LEAN / 'scripts/templates/gkr_worker_ports.lean',
             LEAN / 'scripts/gkr_worker_ports_instances.py']
    digest = hashlib.sha256()
    for path in paths:
        digest.update(path.relative_to(LEAN).as_posix().encode())
        digest.update(b'\0')
        digest.update(path.read_bytes())
    return digest.hexdigest()


def dimensions(case):
    entry = json.loads(DIMENSIONS.read_text())[case]
    if entry['source_sha256'] != fingerprint(case):
        raise ValueError('refresh worker source dimensions: ' + case)
    return entry['columns'], entry['bounds']


def block(text, name):
    start = text.index('noncomputable def ' + name)
    stop = text.index('\n\n', start)
    return text[start:stop] + '\n\n'


def statement(text, name):
    start = text.index('theorem ' + name)
    stop = text.index(' := by decide +kernel', start)
    return text[start:stop]


def input_text(case):
    family, mode, _ = identity(case)
    _, text = legacy.module(family, mode)
    prefix = text[:text.index('theorem original_columns')]
    prefix = prefix.replace('set_option maxHeartbeats 8000000\n', '')
    prefix += block(text, 'logicalValues')
    if family == 'blake-round':
        shared = next(iter(legacy.legacy_modules(family, mode)))[1]
        prefix += block(shared, 'historyPredicate')
    return prefix + 'end Airbender.Compiler.WorkerPortsNative.' + case + '\n'


def header(case):
    return (f'namespace Airbender.Compiler.WorkerPortChecks.{case}\n'
            'open Airbender Airbender.Compiler\nset_option warningAsError true\n'
            'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')


def typed_text(case):
    family, mode, model = identity(case)
    _, text = legacy.module(family, mode)
    worker = 'Airbender.Compiler.WorkerPortsNative.' + case
    memory = 'Airbender.Compiler.MemoryNative.' + case + '.native'
    clean = 'Airbender.Compiler.CleanArithmeticNative.' + case + '.native'
    arithmetic = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    ports = f'Airbender.{model}.importedConstraintsMemoryPorts'
    previous = (f'{arithmetic}.bank.address ({clean}.placement '
                f'(({ports}[index.val]).clock.previous[limb.val]))')
    returned = f'{memory}.bank.address ({memory}.sourcePlacement.readTimestamp index.val limb)'
    predicate = f'(fun index => (List.finRange 2).all (fun limb => decide ({previous} = {returned})))'
    checks = [statement(text, name).split(' :', 1)[1].strip() for name in
              ['original_columns', 'history_columns', 'history_indices']]
    checks[0] = checks[0].replace('originalIndices', worker + '.originalIndices')
    transport = ''
    if family == 'blake-round':
        checks[1] = f'(List.finRange {ports}.size).all {worker}.historyPredicate = true'
        transport = (f'theorem history_predicate : {worker}.historyPredicate = {predicate} := by rfl\n\n')
    return (f'import Airbender.Proofs.GKRProtocol.WorkerPortChecks.{case}.Inputs\n'
        'import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks\n\n' + header(case) +
        f'noncomputable def originalPairs := {worker}.originalIndices.map (fun index =>\n'
        f'  ({arithmetic}.bank.address ({clean}.placement index), '
        f'{memory}.bank.address ({memory}.sourcePlacement.original index)))\n'
        f'noncomputable def historyPairs := (List.finRange {ports}.size).flatMap (fun index =>\n'
        f'  (List.finRange 2).map (fun limb => ({previous}, {returned})))\n'
        f'noncomputable def indexBounds := ({memory}.memoryReadRows ++ {memory}.memoryWriteRows).flatMap '
        f'(fun row => row.fields.flatMap (fun field => field.historyIndices.map (fun index => (index.1, {ports}.size))))\n'
        'noncomputable def original : NumericWorkerPortChecks.Typed := ⟨originalPairs ++ historyPairs, indexBounds⟩\n\n' + transport +
        'theorem original_check (checked : original.check = true) :\n'
        f'    (({checks[0]}) ∧ ({checks[1]})) ∧ ({checks[2]}) := by\n' +
        ('  rw [history_predicate]\n' if transport else '') +
        '  simpa only [original, NumericWorkerPortChecks.Typed.check, originalPairs, historyPairs,\n'
        '    indexBounds, List.all_append, List.all_map, List.all_flatMap, Function.comp_def, Bool.and_eq_true] using checked\n\n'
        f'end Airbender.Compiler.WorkerPortChecks.{case}\n')


def merge(prefix, values, reference, first, leaves, lines):
    if len(leaves) == 1:
        return leaves[0][0]
    middle = len(leaves) // 2
    left, right = leaves[:middle], leaves[middle:]
    left_size = sum(n for _, n in left)
    right_size = sum(n for _, n in right)
    a = merge(prefix, values, reference, first, left, lines)
    b = merge(prefix, values, reference, first + left_size, right, lines)
    size = left_size + right_size
    name = f'{prefix}Node{first}_{size}'
    lines.append(f'theorem {name} : ({values}.drop {first}).take {size} = ({reference}.drop {first}).take {size} :=\n'
        f'  NumericWorkerPortChecks.merge_at {values} {reference} {first} {left_size} {right_size} '
        f'{first + left_size} {size} rfl rfl {a} {b}\n')
    return name


def modules(case):
    columns, bounds = dimensions(case)
    stem = 'Airbender.Proofs.GKRProtocol.WorkerPortChecks.' + case
    end = '\nend Airbender.Compiler.WorkerPortChecks.' + case + '\n'
    yield stem + '.Inputs', input_text(case)
    yield stem + '.Typed', typed_text(case)
    lines, chunks = [], {}
    for field, size, width in [('columns', columns, 16), ('bounds', bounds, 32)]:
        chunks[field] = []
        for first in range(0, size, width):
            amount = min(width, size - first)
            name = field + str(first)
            chunks[field].append(name + '.' + field)
            value = f'(original.{field}.drop {first}).take {amount}'
            source = f'⟨{value}, []⟩' if field == 'columns' else f'⟨[], {value}⟩'
            lines.append(f'numeric_worker_port_capture {name} := NumericWorkerPortChecks.encode ({source})\n')
    lines.append('noncomputable def data : NumericWorkerPortChecks.Data :=\n  ⟨' +
        balanced(chunks['columns']) + ', ' + balanced(chunks['bounds']) + '⟩\n')
    yield stem + '.Data', (f'import {stem}.Typed\nimport Airbender.Import.GKRProtocol.NumericWorkerPortImport\n\n' + header(case) + '\n'.join(lines) + end)
    lines = ['attribute [local irreducible] original data\n']
    encode = '(fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))'
    for field, size, data_width, width in [('columns', columns, 16, 4), ('bounds', bounds, 32, 16)]:
        leaves = []
        reference = '(original.columns.map ' + encode + ')' if field == 'columns' else 'original.bounds'
        for first in range(0, size, width):
            amount = min(width, size - first)
            chunk, offset = first // data_width * data_width, first % data_width
            view = f'({field}{chunk}.{field}.drop {offset}).take {amount}'
            source = f'(original.{field}.drop {first}).take {amount}'
            if field == 'columns':source = '(' + source + ').map ' + encode
            lines += [f'numeric_data_binding {field}{first}_view : (data.{field}.drop {first}).take {amount} = {view}\n',
                      f'numeric_data_binding {field}{first}_piece : {view} = {source}\n']
            proof = f'{field}{first}_view.trans {field}{first}_piece'
            if field == 'columns':
                proof = f'{field}{first}_view.trans ({field}{first}_piece.trans (NumericQueryFrameChecks.map_window original.columns {encode} {first} {amount}))'
            name = f'{field}{first}_binding'
            lines.append(f'theorem {name} : (data.{field}.drop {first}).take {amount} = ({reference}.drop {first}).take {amount} :=\n  {proof}\n')
            leaves.append((name, amount))
        whole = merge(field, 'data.' + field, reference, 0, leaves, lines)
        lines.append(f'theorem {field}_binding : data.{field} = {reference} :=\n'
            f'  NumericQueryFrameChecks.complete_binding data.{field} {reference} {size}\n'
            f'    (by decide +kernel) (by decide +kernel) {whole}\n')
    lines.append('theorem source_binding : data = NumericWorkerPortChecks.encode original := by\n'
        '  simpa only [data, NumericWorkerPortChecks.encode] using\n'
        '    congrArg₂ NumericWorkerPortChecks.Data.mk columns_binding bounds_binding\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header(case) + '\n'.join(lines) + end)
    yield stem + '.Certificate', (f'import {stem}.Bindings\n\n' + header(case) +
        'theorem checked : NumericWorkerPortChecks.check data = true := by decide +kernel\n\n'
        'theorem originalChecked : original.check = true :=\n'
        '  NumericWorkerPortChecks.check_sound original data source_binding checked\n\n'
        'def facts := original_check originalChecked\n' + end)


def native(case):
    family, mode, model = identity(case)
    target, text = legacy.module(family, mode)
    for name in ['originalIndices', 'logicalValues']:
        text = text.replace(block(text, name), '')
    numeric = 'Airbender.Compiler.WorkerPortChecks.' + case + '.facts'
    for name, projection in [('original_columns', '.1.1'), ('history_columns', '.1.2'), ('history_indices', '.2')]:
        old = statement(text, name)
        new = old
        if family == 'blake-round' and name == 'history_columns':
            new = f'theorem history_columns : (List.finRange Airbender.{model}.importedConstraintsMemoryPorts.size).all historyPredicate = true'
        text = text.replace(old + ' := by decide +kernel', new + ' := ' + numeric + projection)
    text = text[text.index('namespace Airbender.Compiler.WorkerPortsNative.'):]
    text = text.replace('set_option maxHeartbeats 8000000\n', '')
    # Preserve the old shard declarations as corollaries of the complete result.
    if family == 'blake-round':
        size = len(json.loads((LEAN / f'artifacts/compiler/{family}-{mode}.json').read_text())['circuit']['memory_layout']['ram_access_sets'])
        items = f'(List.finRange Airbender.{model}.importedConstraintsMemoryPorts.size)'
        lines = []
        for first in range(0, size, 4):
            stop = min(first + 4, size); name = 'historyPart' + str(first)
            for index in range(first, stop):
                item = f'{items}.get ⟨{index}, by decide +kernel⟩'
                lines.append(f'theorem {name}Item{index} : historyPredicate ({item}) = true :=\n'
                    f'  List.all_eq_true.mp history_columns _ (List.get_mem _ _)\n')
            lines.append(f'noncomputable def {name}Block := ({items}.drop {first}).take {stop - first}\n')
            lines.append(f'theorem {name} : {name}Block.all historyPredicate = true := by\n'
                '  apply List.all_eq_true.mpr\n  intro index member\n  apply List.all_eq_true.mp history_columns index\n'
                '  exact List.mem_of_mem_drop (List.mem_of_mem_take member)\n')
        pos = text.index('theorem source_read_tokens')
        text = text[:pos] + '\n'.join(lines) + '\n' + text[pos:]
    return target, f'import Airbender.Proofs.GKRProtocol.WorkerPortChecks.{case}.Certificate\n\n' + text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=CASES, action='append')
    for flag in ['write', 'check']:parser.add_argument('--' + flag, action='store_true')
    args = parser.parse_args()
    generated = [entry for case in args.case or CASES for entry in [*modules(case), native(case)]]
    if args.write:preflight({LEAN / (module.replace('.', '/') + '.lean'): text for module, text in generated})
    for module, text in generated:
        path = LEAN / (module.replace('.', '/') + '.lean')
        if args.write:path.parent.mkdir(parents=True, exist_ok=True);path.write_text(text)
        if args.check and (not path.exists() or path.read_text() != text):raise SystemExit('stale worker checks: ' + str(path))
    print('PASS complete worker captures:', len(args.case or CASES))


if __name__ == '__main__':main()
