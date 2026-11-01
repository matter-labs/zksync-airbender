#!/usr/bin/env python3
"""Bind all counter-frame data before one complete natural-number check."""
import argparse
import json

from export_gkr_translations import LEAN
from gkr_full_arithmetic_certificate import synthesize
from gkr_packed_query_frame import capture_name
from gkr_packed_rotate_boundary import preflight
from gkr_wiring_instances import CASES as CIRCUIT_CASES

PILOT_CASES = ('AddSubCached', 'AddSubUncached')
CASES = PILOT_CASES + tuple(stem + mode for stem in CIRCUIT_CASES if stem != 'AddSub'
                           for mode in ['Cached', 'Uncached'])


def dimensions(case):
    name = capture_name(case)
    pair = json.loads((LEAN / f'artifacts/compiler/{name}.json').read_text())
    source = json.loads((LEAN / f'artifacts/compiler/{name}-source.json').read_text())
    arity = len(synthesize(pair, source)['inputs'])
    kinds = {'GenericLookup': 'generic_lookup', 'Lookup16Bits': 'range_check_16',
             'LookupTimestamps': 'timestamp_range_check'}
    columns = [pair['circuit']['witness_layout']['multiplicities_columns_for_' + kinds[kind]]['start']
               for kind in pair['circuit']['global_output_map'] if kind in kinds]
    return name, pair['source']['num_variables'], arity, columns


def modules(case):
    name, source_count, arity, columns = dimensions(case)
    native = 'Airbender.Compiler.CounterFrameNative.' + case + '.native'
    base = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    table = 'Airbender.Compiler.TableNative.' + case + '.native'
    helper = 'Airbender.Compiler.HelperNative.' + case + '.native'
    owner = 'Airbender.Compiler.CounterFrameChecks.' + case
    stem = 'Airbender.Proofs.GKRProtocol.CounterFrameChecks.' + case
    header = (f'namespace {owner}\nopen Airbender.Compiler\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end = '\nend ' + owner + '\n'
    yield stem + '.Inputs', (
        'import Airbender.Import.GKRProtocol.CounterFrameImport\n'
        f'import Airbender.Proofs.GKRProtocol.HelperValidityNative.{case}\n'
        f'import Airbender.Proofs.GKRProtocol.TableNative.{case}\n\n'
        f'namespace Airbender.Compiler.CounterFrameNative.{case}\n'
        'open Airbender Airbender.Compiler\nset_option warningAsError true\n'
        'set_option Elab.async false\nset_option maxRecDepth 32768\n\n'
        f'import_counter_frame native from "artifacts/compiler/{name}.json"\n'
        f'  base_model {base}\n  table_model {table}\n  helper_model {helper} inputs {arity} phase 0\n\n'
        f'end Airbender.Compiler.CounterFrameNative.{case}\n')
    expression = (f'NumericCounterFrameChecks.ofTyped {table}.multiplicityColumns {columns} {native}.slots '
                  f'{base}.inputBank {base}.artifact.source '
                  f'({helper}.fields.map (fun field => field.polynomial {base}.helperPlacement))')
    yield stem + '.Data', (f'import {stem}.Inputs\n'
        'import Airbender.Import.GKRProtocol.NumericCounterFrameImport\n\n' + header +
        'numeric_counter_frame_capture data := ' + expression + '\n' + end)
    yield stem + '.Bindings', (f'import {stem}.Data\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n' + header +
        'numeric_data_binding source_binding : data = ' + expression + '\n' + end)
    yield stem + '.Certificate', (f'import {stem}.Bindings\n\n' + header +
        f'theorem checked : NumericCounterFrameChecks.check {source_count} data = true := by decide +kernel\n\n'
        'theorem originalChecked :\n'
        f'  {table}.multiplicityColumns = {columns} ∧ Function.Injective {native}.slots ∧\n'
        f'  (∀ index, {source_count} ≤ ({native}.slots index).val) ∧\n'
        f'  (∀ index, {base}.inputBank.address ({native}.slots index) =\n'
        f'    GKRAddress.BaseLayerWitness ({table}.multiplicityColumns.get index)) ∧\n'
        f'  {base}.artifact.source.all (erasureUntouched (List.ofFn {native}.slots)) = true ∧\n'
        f'  ({helper}.fields.map (fun field => field.polynomial {base}.helperPlacement)).all\n'
        f'    (erasureUntouched (List.ofFn {native}.slots)) = true :=\n'
        f'  NumericCounterFrameChecks.check_sound data {source_count} {table}.multiplicityColumns {columns} {native}.slots\n'
        f'    {base}.inputBank {base}.artifact.source\n'
        f'    ({helper}.fields.map (fun field => field.polynomial {base}.helperPlacement)) source_binding checked\n' + end)


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
                raise ValueError('counter frame capture changed: ' + module)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(module)


if __name__ == '__main__':
    main()
