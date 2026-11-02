#!/usr/bin/env python3
"""Bind original and erased polynomials before one exact history check."""
import argparse
import json

from export_gkr_translations import LEAN
from gkr_full_arithmetic_certificate import synthesize
from gkr_packed_query_frame import capture_name
from gkr_packed_rotate_boundary import preflight
from gkr_wiring_instances import CASES as CIRCUIT_CASES

PILOT_CASES = ('AddSubCached',)
CASES = PILOT_CASES + tuple(stem + mode for stem in CIRCUIT_CASES if stem != 'AddSub'
                           for mode in ['Cached'])


def dimensions(case):
    name = capture_name(case)
    pair = json.loads((LEAN / f'artifacts/compiler/{name}.json').read_text())
    source = json.loads((LEAN / f'artifacts/compiler/{name}-source.json').read_text())
    return name, len(synthesize(pair, source)['inputs'])


def modules(case):
    name, arity = dimensions(case)
    native = 'Airbender.Compiler.HistoryErasureNative.' + case + '.native'
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    source = 'Airbender.Compiler.SourceContractNative.' + case + '.native'
    owner = 'Airbender.Compiler.HistoryErasureChecks.' + case
    stem = 'Airbender.Proofs.GKRProtocol.HistoryErasureChecks.' + case
    header = (f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end = '\nend ' + owner + '\n'
    yield stem + '.Inputs', (
        'import Airbender.Import.GKRProtocol.HistoryErasureImport\n'
        f'import Airbender.Proofs.GKRProtocol.SourceContractNative.{case}\n\n'
        f'namespace Airbender.Compiler.HistoryErasureNative.{case}\n'
        'open Airbender Airbender.Compiler\nset_option warningAsError true\n'
        'set_option Elab.async false\nset_option maxRecDepth 32768\n\n'
        f'import_history_erasure native from "artifacts/compiler/{name}-source.json"\n'
        f'  base_model {base}\n  source_model {source} inputs {arity} phase 0\n\n'
        f'end Airbender.Compiler.HistoryErasureNative.{case}\n')
    fields = f'({native}.protectedFields.map (fun field => field.polynomial {base}.helperPlacement.memory))'
    expression = f'NumericHistoryErasureChecks.ofTyped {native}.historyCells {source}.protectedPolynomials {fields}'
    fast_expression = (f'NumericHistoryErasureChecks.ofSource {native}.historyCells {source}.originals '
                       f'{source}.clock {base}.helperPlacement {fields}')
    yield stem + '.Data', (f'import {stem}.Inputs\n'
        'import Airbender.Import.GKRProtocol.NumericHistoryErasureImport\n\n' +
        header +
        'numeric_history_erasure_capture data := ' + fast_expression + '\n' + end)
    yield stem + '.Bindings', (f'import {stem}.Data\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header +
        'numeric_data_binding fast_binding : data = ' + fast_expression + '\n\n' +
        'theorem source_binding : data = ' + expression + ' := by\n' +
        f'  have actual := fast_binding.trans (NumericHistoryErasureChecks.ofSource_eq {native}.historyCells\n'
        f'    {source}.originals {source}.clock {base}.helperPlacement {fields})\n'
        f'  simpa only [{source}.protectedPolynomials, {source}.clockPolynomials] using actual\n' + end)
    yield stem + '.Certificate', (f'import {stem}.Bindings\n\n' + header +
        'private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩\n\n'
        'theorem checked : NumericHistoryErasureChecks.check babyBearModulus data = true := by decide +kernel\n\n'
        f'theorem originalChecked : {native}.historyCells.Nodup ∧\n'
        f'  erasureCheck {native}.historyCells {source}.protectedPolynomials = true ∧\n'
        f'  {fields}.all (fun polynomial => equal\n'
        f'    (substitute (erasurePolynomials {native}.historyCells) polynomial) polynomial) = true :=\n'
        f'  NumericHistoryErasureChecks.check_sound data {native}.historyCells\n'
        f'    {source}.protectedPolynomials {fields} source_binding checked\n' + end)


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
                raise ValueError('history erasure capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(module)


if __name__ == '__main__':
    main()
