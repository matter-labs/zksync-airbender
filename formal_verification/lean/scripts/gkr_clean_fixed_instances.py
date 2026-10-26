#!/usr/bin/env python3
"""Discharge retained Jump/MUL fixed lookups through actual tagged setup regions."""
import argparse
import json
import os
import re
import subprocess
from export_gkr_translations import LEAN
from gkr_clean_closed_instances import module as full_table_module

FAMILIES = {'jump-branch': ('JumpBranch', 'JumpBranchSlt'), 'mul-div': ('MulDiv', 'MulDiv')}
TABLES = {1: ('regIsZeroTable', 2), 2: ('jumpCleanupTable', 3), 5: ('u16SignTable', 2),
          31: ('conditionalTable', 2), 41: ('u16LowByteTable', 2), 26: ('range13Table', 1)}


def module(family, stem, model_name, mode):
    name, case = family + '-' + mode, stem + mode.title()
    pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
    cert = json.loads((LEAN / 'artifacts/compiler/lookup' / (name + '.json')).read_text())
    width = pair['circuit']['generic_lookup_tables_width']
    # Reuse the unchanged scalar proofs; full-table generic proofs are replaced below.
    _, scalar_template = full_table_module(name, case, model_name, width)
    scalar_text = scalar_template[scalar_template.index('theorem range_lookup'):
                                  scalar_template.index('theorem generic_lookup')]
    arity = re.search(r'\(sourceValue : Fin (\d+)', scalar_text).group(1)
    prefix = 'Airbender.Compiler.'
    o = {key: prefix + model + '.' + case + '.native' for key, model in [
        ('args', 'CleanArgumentsNative'), ('generic', 'CleanGenericArgumentsNative'),
        ('base', 'FullArithmeticNative'), ('fields', 'LookupNative'), ('queries', 'LookupSourceNative'),
        ('frame', 'QueryFrameNative'), ('counter', 'CounterFrameNative'), ('helper', 'HelperValidityNative'),
        ('helperfields', 'HelperNative'), ('setup', 'MaterializedNative'), ('table', 'TableNative'),
        ('clean', 'CleanArithmeticNative')]}
    native_fixed = prefix + 'FixedSetupNative.' + stem
    namespace = prefix + 'CleanClosedNative.' + case
    imports = ['Airbender.Proofs.GKRProtocol.CleanArgumentsNative.' + case, 'Airbender.Proofs.GKRProtocol.CleanScalarNative.' + case,
               'Airbender.Proofs.GKRProtocol.CleanGenericArgumentsNative.' + case, 'Airbender.Proofs.GKRProtocol.FixedPrimitives',
               'Airbender.Proofs.GKRProtocol.FixedSetupNative.' + stem + 'Membership', 'Airbender.Proofs.GKRProtocol.CleanLinksNative.' + case,
               'Airbender.Proofs.GKRProtocol.MaterializedWitnessNative.' + case, 'Airbender.Proofs.Constraints']
    text = ''.join('import ' + item + '\n' for item in imports)
    text += (f'\nnamespace {namespace}\nopen Airbender Airbender.Compiler\n'
             'set_option warningAsError true\nset_option Elab.async false\n'
             'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n')
    generic_rows = sorted([(row, i) for i, row in enumerate(cert['rows']) if row['kind'] == 'generic'],
                          key=lambda item: item[0]['native_index'])
    fixed = []
    details = []
    inverse = pow(268435454, -1, 2013265921)
    for row, row_index in generic_rows:
        i, n = row['source_index'], row['native_index']
        tag = pair['circuit']['generic_lookups'][n]['columns'][-1]['constant'] * inverse % 2013265921
        table, fields = TABLES[tag]
        expressions = [o['generic'] + f'.part{n//8}.genericExpression{i}_{col}' for col in range(fields)]
        if fields == 1:
            lookup = 'Verification.range13 ' + expressions[0]
        elif fields == 2:
            lookup = 'Verification.pairLookup Verification.' + table + ' ' + ' '.join(expressions)
        else:
            lookup = 'Verification.jumpCleanup ' + ' '.join(expressions)
        text += f'noncomputable def fixedLookup{n} : Lookup Source.BaseField :=\n  {lookup}\n\n'
        fixed.append('fixedLookup' + str(n))
        details.append((row, row_index, tag, fields))
    text += 'noncomputable def fixedLookups : List (Lookup Source.BaseField) := [' + ', '.join(fixed) + ']\n\n'
    operations = f'(Airbender.{model_name}.clockConstraints (p := babyBearModulus))'
    environment = f'({o["clean"]}.environment physical data)'
    text += (f'theorem clock_lookup_inventory :\n    FlatOperation.lookups {operations} =\n'
             f'    ({o["args"]}.rangeExpressions.map Verification.range16) ++ fixedLookups ++\n'
             f'      ({o["args"]}.timestampExpressions.map Trace.timestampLookup) := by rfl\n\n' + scalar_text)
    common = (f'    (sourceValue : Fin {arity} → Source.BaseField)\n'
              f'    (counts : Fin {o["table"]}.multiplicityColumns.length → Source.BaseField)\n'
              '    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n'
              f'    (inputAgreement : ∀ wire, physical ({o["base"]}.inputBank.address wire) = {o["counter"]}.assigned ({o["helper"]}.canonical sourceValue) counts wire)\n'
              f'    (arithmetic : ∀ gate ∈ {o["base"]}.artifact.gates, gate.expressionResidual (physical ∘ {o["base"]}.bank.address) = 0)\n')
    authored = f'    (authored : {prefix}MaterializedWitnessNative.{case}.AuthoredLookupValid sourceValue)'
    projection = f'(sourceValue ∘ {o["base"]}.originalProjection)'
    generic_proofs = []
    for row, row_index, tag, fields in details:
        i, n = row['source_index'], row['native_index']
        text += f'theorem generic_lookup{i}\n' + common + authored + f' :\n    fixedLookup{n}.Contains {environment} := by\n'
        text += (f'  let query := {o["queries"]}.genericQueries.get ⟨{i}, by decide⟩\n'
                 f'  have member := authored.1 query (List.get_mem {o["queries"]}.genericQueries ⟨{i}, by decide⟩)\n'
                 f'  have nonzero : query.weight (RingHom.id _) {projection} ≠ 0 := by\n'
                 '    change (1 : Source.BaseField) ≠ 0\n    exact one_ne_zero\n'
                 '  obtain ⟨setupRow, dataRow⟩ := member nonzero\n'
                 f'  have tagProof := congrArg (fun entries : List Source.BaseField => entries.getD {width-1} 0) dataRow\n'
                 f'  change ({tag} : Source.BaseField) = {o["setup"]}.model.value setupRow (.generic {width-1}) at tagProof\n'
                 f'  have selected : {native_fixed}.nativeSetup.value setupRow (.generic {width-1}) = {tag} := tagProof.symm\n')
        for col in range(fields):
            field = o['fields'] + f'.field{row_index}_{col}'
            text += (f'  have present{col} : {field}.source ∈ {o["frame"]}.fields := List.get_mem {o["frame"]}.fields ⟨{i*width+col}, by decide⟩\n'
                     f'  have transported{col} := {o["frame"]}.fields_preserved sourceValue counts physical inputAgreement {field}.source present{col}\n'
                     f'  have sourceCell{col} := congrArg (fun entries : List Source.BaseField => entries.getD {col} 0) dataRow\n'
                     f'  change {field}.source.value {projection} = {o["setup"]}.model.value setupRow (.generic {col}) at sourceCell{col}\n'
                     f'  have same{col} := ({o["generic"]}.part{n//8}.generic_value{i}_{col} physical data arithmetic).trans (transported{col}.trans sourceCell{col})\n')
        if fields == 1:
            text += ('  apply Verification.range13_contains\n  rw [same0]\n'
                     f'  exact {native_fixed}.range13_value_bound setupRow selected\n\n')
        else:
            text += ('  apply clean_' + ('pair' if fields == 2 else 'triple') + '_lookup\n'
                     '  rw [' + ', '.join('same'+str(c) for c in range(fields)) + ']\n'
                     f'  exact {native_fixed}.tag{tag}_contains setupRow selected _\n\n')
        generic_proofs.append(f'generic_lookup{i} sourceValue counts physical data inputAgreement arithmetic authored')
    range_rows = sorted([row for row in cert['rows'] if row['kind'] == 'range16'], key=lambda row: row['native_index'])
    proofs = [f'range_lookup{row["source_index"]} sourceValue counts physical data inputAgreement arithmetic authored' for row in range_rows]
    proofs += generic_proofs
    proofs += [f'clean_timestamp_lookup {o["args"]}.timestampExpression{i} {environment} ({o["args"]}.timestamp_bound{i} physical data arithmetic helpers)'
               for i in range(len(pair['circuit']['timestamp_range_check_lookup_expressions']))]
    tree = 'PredicateChecks.nil'
    for proof in reversed(proofs):
        tree = f'(PredicateChecks.cons ({proof}) {tree})'
    text += ('theorem retained_clock_from_source\n' + common +
             f'    (helpers : ∀ field ∈ {o["helperfields"]}.fields, (field.value ({o["helperfields"]}.sourceValues physical)).val < 524288)\n' + authored + ' :\n'
             f'    FlatOperation.ConstraintsHoldFlat {environment} {operations} := by\n'
             f'  apply {prefix}CleanLinksNative.{case}.retained_clock_constraints physical data arithmetic\n'
             f'  rw [clock_lookup_inventory]\n  exact PredicateChecks.all {tree}\n\nend {namespace}\n')
    return 'Airbender.Proofs.GKRProtocol.CleanClosedNative.' + case, text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, (stem, model) in FAMILIES.items():
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            target, text = module(family, stem, model, mode)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('retained fixed lookup adapter changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(target, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
