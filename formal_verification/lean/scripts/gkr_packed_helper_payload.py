#!/usr/bin/env python3
"""Bind complete helper payload checks to the original candidates."""
import argparse
import json
from export_gkr_translations import LEAN, FAMILIES
from gkr_wiring_instances import CASES as STEMS
import gkr_helper_instances as legacy
from gkr_packed_functional_steps import balanced
from gkr_packed_worker_ports import merge
from gkr_packed_rotate_boundary import preflight

ALL_CASES = tuple(stem + mode for stem in STEMS for mode in ('Cached', 'Uncached'))
CASES = ALL_CASES


def capture_name(case):
    for family, stem in zip(FAMILIES, STEMS, strict=True):
        for mode in ('Cached', 'Uncached'):
            if case == stem + mode:
                return family + '-' + mode.lower()
    raise ValueError('unknown helper payload capture: ' + case)


def selectors(case):
    name = capture_name(case)
    root = LEAN / 'artifacts/compiler'
    return legacy.synthesis(json.loads((root / (name + '.json')).read_text()),
                            json.loads((root / (name + '-source.json')).read_text()),
                            json.loads((root / 'lookup' / (name + '.json')).read_text()))


def inputs(case):
    text = legacy.module(capture_name(case), case)[1]
    text = text.replace('set_option maxHeartbeats 4000000\n', '')
    from gkr_packed_memory_payload import CASES as memory_cases
    if case in memory_cases:
        text = text.replace('set_option maxRecDepth 32768\n\n',
            'set_option maxRecDepth 32768\n\n'
            '-- Keep the original data instance paths after numeric memory imports.\n'
            'attribute [local instance 2000] ZMod.commRing CommSemiring.toSemiring CommRing.toCommSemiring\n\n')
    if case.startswith('BlakeRound'):
        text = text.replace('import_source_helpers native',
            '-- This command reconstructs every original affine definition.\n'
            '-- The default budget expires on the complete data phase.\n'
            'set_option maxHeartbeats 2000000 in\nimport_source_helpers native')
    return text.replace('\n\nend Airbender.Compiler.HelperNative.', ' phase 0\n\nend Airbender.Compiler.HelperNative.')


def source(case, leaf):
    return (f'NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.{case}.native.candidate{leaf}\n'
            f'  Airbender.Compiler.HelperNative.{case}.native.placement Airbender.Compiler.MemoryNative.{case}.native.bank\n'
            f'  Airbender.Compiler.ConsumerNative.{case}.native.typing')


def header(case):
    return (f'namespace Airbender.Compiler.HelperPayloadChecks.{case}\n'
            'open Airbender Airbender.Compiler\nset_option warningAsError true\n'
            'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')


def modules(case):
    ids = [row['native_leaf'] for row in selectors(case)['operands']]
    if len(ids) != len(set(ids)) or not ids:
        raise ValueError('helper payload selectors must be nonempty and unique')
    stem = 'Airbender.Proofs.GKRProtocol.HelperPayloadChecks.' + case
    end = '\nend Airbender.Compiler.HelperPayloadChecks.' + case + '\n'
    yield stem + '.Inputs', inputs(case)
    yield stem + '.Typed', (f'import {stem}.Inputs\nimport Airbender.Proofs.GKRProtocol.NumericNativePayloadChecks\n\n'
        + header(case) + 'noncomputable def originalEntries := [\n  '
        + ',\n  '.join(source(case, leaf) for leaf in ids) + ']\n' + end)
    chunks, lines = [], []
    for first in range(0, len(ids), 4):
        chunk = 'data' + str(first)
        chunks.append(chunk)
        lines.append('numeric_functional_base_capture ' + chunk + ' := [\n  '
            + ',\n  '.join('NumericFunctionalBaseChecks.encode (' + source(case, leaf) + ')'
                          for leaf in ids[first:first + 4]) + ']\n')
    lines.append('noncomputable def data : List NumericFunctionalBaseChecks.Data := ' + balanced(chunks) + '\n')
    yield stem + '.Data', (f'import {stem}.Typed\nimport Airbender.Import.GKRProtocol.NumericFunctionalBaseImport\n\n'
                          + header(case) + '\n'.join(lines) + end)
    lines = ['attribute [local irreducible] originalEntries data\n']
    leaves = []
    for index, leaf in enumerate(ids):
        chunk, offset = index // 4 * 4, index % 4
        lines.append(f'numeric_data_binding row{index}_view : (data.drop {index}).take 1 = (data{chunk}.drop {offset}).take 1\n')
        lines.append(f'numeric_data_binding row{index}_source : (data{chunk}.drop {offset}).take 1 = [NumericFunctionalBaseChecks.encode ({source(case, leaf)})]\n')
        lines.append(f'numeric_data_binding row{index}_entry : ((originalEntries.drop {index}).take 1).map NumericFunctionalBaseChecks.encode = [NumericFunctionalBaseChecks.encode ({source(case, leaf)})]\n')
        lines.append(f'theorem row{index}_binding : (data.drop {index}).take 1 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop {index}).take 1 :=\n'
            f'  row{index}_view.trans (row{index}_source.trans (row{index}_entry.symm.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode {index} 1)))\n')
        leaves.append((f'row{index}_binding', 1))
    whole = merge('entries', 'data', '(originalEntries.map NumericFunctionalBaseChecks.encode)', 0, leaves, lines)
    lines.append(f'theorem source_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=\n'
        f'  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) {len(ids)}\n'
        f'    (by decide +kernel) (by decide +kernel) {whole}\n')
    yield stem + '.Bindings', (f'import {stem}.Data\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n'
        'import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks\n\n' + header(case) + '\n'.join(lines) + end)
    lines = ['theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel\n']
    for index, leaf in enumerate(ids):
        original = f'Airbender.Compiler.HelperNative.{case}.native'
        bank = f'Airbender.Compiler.MemoryNative.{case}.native.bank'
        typing = f'Airbender.Compiler.ConsumerNative.{case}.native.typing'
        lines.append(f'theorem operand{leaf} : ({original}.candidate{leaf}).check {original}.placement {bank} = true ∧\n'
            f'    ({bank}).check {original}.recipe{leaf} = true ∧\n'
            f'    (NativeLookupEncoding.scalar {original}.recipe{leaf}).baseCheck {typing} = true := by\n'
            f'  have valid := NumericNativePayloadChecks.checked_at ({source(case, leaf)}) data {index}\n'
            f'    (row{index}_view.trans row{index}_source) checked\n'
            f'  rw [NumericNativePayloadChecks.ofHelper_check] at valid\n'
            f'  simp only [Bool.and_eq_true] at valid\n'
            f'  exact ⟨valid.2, valid.1.1, valid.1.2⟩\n')
    yield stem + '.Certificate', f'import {stem}.Bindings\n\n' + header(case) + '\n'.join(lines) + end


def native(case):
    text = legacy.module(capture_name(case), case)[1]
    text = text[text.index('namespace Airbender.Compiler.HelperNative.'):]
    text = text.replace('set_option maxHeartbeats 4000000\n', '')
    text = text.replace('\n\nend Airbender.Compiler.HelperNative.',
                        ' phase 1 using_checks Airbender.Compiler.HelperPayloadChecks.' + case
                        + '\n\nend Airbender.Compiler.HelperNative.')
    return ('Airbender.Proofs.GKRProtocol.HelperNative.' + case,
            'import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.' + case + '.Certificate\n\n' + text)


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
            raise SystemExit('stale helper payload: ' + str(path))
    print('PASS complete helper payload captures:', len(args.case or CASES))


if __name__ == '__main__':
    main()
