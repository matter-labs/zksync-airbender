#!/usr/bin/env python3
"""Discharge retained Clean lookup premises from source membership and helper bounds."""
import argparse
import json
import os
import re
import subprocess
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_clean_links import MODELS, WIDTHS


def module(name, case, model_name, width):
    if not width and not name.startswith('add-sub-'):
        raise ValueError('fixed-table projection adapter is not implemented: ' + name)
    pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
    cert = json.loads((LEAN / 'artifacts/compiler/lookup' / (name + '.json')).read_text())
    prior = (LEAN / 'GKRProtocol/MaterializedWitnessNative' / (case + '.lean')).read_text()
    arity = re.search(r'\(sourceValue : Fin (\d+)', prior).group(1)
    prefix = 'Airbender.Compiler.'
    o = {key: prefix + model + '.' + case + '.native' for key, model in [
        ('args', 'CleanArgumentsNative'), ('generic', 'CleanGenericArgumentsNative'),
        ('base', 'FullArithmeticNative'), ('fields', 'LookupNative'), ('queries', 'LookupSourceNative'),
        ('frame', 'QueryFrameNative'), ('counter', 'CounterFrameNative'), ('helper', 'HelperValidityNative'),
        ('helperfields', 'HelperNative'), ('setup', 'MaterializedNative'), ('table', 'TableNative'),
        ('scalars', 'CleanScalarNative'), ('clean', 'CleanArithmeticNative')]}
    setup_model = o['setup'] + '.model'
    namespace = prefix + 'CleanClosedNative.' + case
    imports = ['GKRProtocol.CleanArgumentsNative.' + case, 'GKRProtocol.CleanScalarNative.' + case,
               'GKRProtocol.CleanPrimitiveLookups', 'GKRProtocol.CleanLinksNative.' + case,
               'GKRProtocol.MaterializedWitnessNative.' + case]
    if width:
        imports += ['GKRProtocol.CleanGenericArgumentsNative.' + case, 'GKRProtocol.CleanGenericSetup']
    s = ''.join('import ' + item + '\n' for item in imports)
    s += (f'\nnamespace {namespace}\nopen Airbender Airbender.Compiler\n'
          'set_option warningAsError true\nset_option Elab.async false\n'
          'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n')
    if width:
        s += (f'noncomputable def nativeSetup : Table Source.BaseField (fields {width}) :=\n'
              f'  {setup_model}.imported.data.table "Airbender.Native.{model_name}"\n\n'
              f'theorem generic_columns_inventory : {o["table"]}.genericSetupColumns =\n'
              f'    (List.range {width}).map SourceSetupColumn.generic := by decide +kernel\n\n')
    worker = model_name in ['Bigint', 'Blake2G', 'Blake2Round', 'Keccak']
    alignment_start = 1 + 2 * len(pair['circuit']['memory_layout']['ram_access_sets'])
    operations = f'(Airbender.{model_name}.clockConstraints (p := babyBearModulus)' + (' nativeSetup)' if width else ')')
    parts = [f'({o["args"]}.rangeExpressions.map Verification.range16)']
    if worker:
        parts += [f'(({o["args"]}.timestampExpressions.drop {alignment_start}).map Trace.timestampLookup)']
    if width:
        parts += [f'({o["generic"]}.genericExpressions.map (fun entry => Lookup.mk nativeSetup.toRaw entry))']
    parts += [f'({o["args"]}.timestampExpressions.map Trace.timestampLookup)']
    s += ('theorem clock_lookup_inventory :\n    FlatOperation.lookups ' + operations + ' =\n    ' +
          ' ++\n    '.join(parts) + ' := by rfl\n\n')
    common = (f'    (sourceValue : Fin {arity} → Source.BaseField)\n'
              f'    (counts : Fin {o["table"]}.multiplicityColumns.length → Source.BaseField)\n'
              '    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n'
              f'    (inputAgreement : ∀ wire, physical ({o["base"]}.inputBank.address wire) = {o["counter"]}.assigned ({o["helper"]}.canonical sourceValue) counts wire)\n'
              f'    (arithmetic : ∀ gate ∈ {o["base"]}.artifact.gates, gate.expressionResidual (physical ∘ {o["base"]}.bank.address) = 0)\n')
    authored = f'    (authored : {prefix}MaterializedWitnessNative.{case}.AuthoredLookupValid sourceValue)'
    projection = f'(sourceValue ∘ {o["base"]}.originalProjection)'
    environment = f'({o["clean"]}.environment physical data)'
    # QueryFrame's list follows generic + decoder + range query order.
    generic_rows = sorted([(row, i) for i, row in enumerate(cert['rows']) if row['kind'] == 'generic'],
                          key=lambda item: item[0]['source_index'])
    range_rows = sorted([(row, i) for i, row in enumerate(cert['rows']) if row['kind'] == 'range16'],
                        key=lambda item: item[0]['native_index'])
    offset = sum(len(row['fields']) for row in cert['rows'] if row['kind'] != 'range16')
    range_proofs = []
    for r, row_index in range_rows:
        i = r['source_index']
        field = o['fields'] + f'.field{row_index}_0'
        s += f'theorem range_lookup{i}\n' + common + authored + f' :\n    (Verification.range16 {o["args"]}.rangeExpression{i}).Contains {environment} := by\n'
        s += (f'  let query := {o["queries"]}.range16Queries.get ⟨{i}, by decide⟩\n'
              f'  have member := authored.2 query (List.get_mem {o["queries"]}.range16Queries ⟨{i}, by decide⟩)\n'
              f'  have nonzero : query.weight (RingHom.id _) {projection} ≠ 0 := by\n'
              '    change (1 : Source.BaseField) ≠ 0\n    exact one_ne_zero\n'
              f'  have valid : {setup_model}.Contains [SourceSetupColumn.range16] [{field}.source.value {projection}] := member nonzero\n'
              f'  have present : {field}.source ∈ {o["frame"]}.fields := List.get_mem {o["frame"]}.fields ⟨{offset+i}, by decide⟩\n'
              f'  have transported := {o["frame"]}.fields_preserved sourceValue counts physical inputAgreement {field}.source present\n'
              f'  have same := ({o["args"]}.range_value{i} physical data arithmetic).trans transported\n'
              '  apply clean_scalar_lookup\n  rw [same]\n'
              f'  exact {o["scalars"]}.range16_clean_refinement _ valid _\n\n')
        range_proofs.append(f'range_lookup{i} sourceValue counts physical data inputAgreement arithmetic authored')
    generic_proofs = []
    offset = 0
    generic_authored = 'authored.1' if range_rows else 'authored'
    for r, row_index in generic_rows:
        i, native_index = r['source_index'], r['native_index']
        entry = o['generic'] + f'.genericExpressions{native_index}'
        s += f'theorem generic_lookup{i}\n' + common + authored + f' :\n    (Lookup.mk nativeSetup.toRaw {entry}).Contains {environment} := by\n'
        s += (f'  let query := {o["queries"]}.genericQueries.get ⟨{i}, by decide⟩\n'
              f'  have member := {generic_authored} query (List.get_mem {o["queries"]}.genericQueries ⟨{i}, by decide⟩)\n'
              f'  have nonzero : query.weight (RingHom.id _) {projection} ≠ 0 := by\n'
              '    change (1 : Source.BaseField) ≠ 0\n    exact one_ne_zero\n'
              f'  have valid := member nonzero\n')
        for col in range(width):
            field = o['fields'] + f'.field{row_index}_{col}'
            s += (f'  have present{col} : {field}.source ∈ {o["frame"]}.fields := List.get_mem {o["frame"]}.fields ⟨{offset+col}, by decide⟩\n'
                  f'  have transported{col} := {o["frame"]}.fields_preserved sourceValue counts physical inputAgreement {field}.source present{col}\n'
                  f'  have same{col} := ({o["generic"]}.part{native_index//8}.generic_value{i}_{col} physical data arithmetic).trans transported{col}\n')
        s += ('  apply clean_vector_lookup\n'
              f'  apply {setup_model}.generic_clean_contains {o["table"]}.genericSetupColumns generic_columns_inventory _ ?_ "Airbender.Native.{model_name}" _\n')
        lhs = ', '.join(f'{o["generic"]}.part{native_index//8}.genericExpression{i}_{col}.eval {environment}' for col in range(width))
        rhs = ', '.join(f'{o["fields"]}.field{row_index}_{col}.source.value {projection}' for col in range(width))
        s += f'  simp only [{entry}, Vector.map_mk, List.map_toArray]\n'
        s += f'  change {setup_model}.Contains {o["table"]}.genericSetupColumns [{lhs}]\n'
        s += '  rw [' + ', '.join('same' + str(col) for col in range(width)) + ']\n  exact valid\n\n'
        offset += width
        generic_proofs.append((native_index, f'generic_lookup{i} sourceValue counts physical data inputAgreement arithmetic authored'))
    helper_binder = f'    (helpers : ∀ field ∈ {o["helperfields"]}.fields, (field.value ({o["helperfields"]}.sourceValues physical)).val < 524288)\n'
    s += ('theorem retained_clock_from_source\n' + common + helper_binder + authored + ' :\n'
          f'    FlatOperation.ConstraintsHoldFlat {environment} {operations} := by\n'
          f'  apply {prefix}CleanLinksNative.{case}.retained_clock_constraints ' + ('nativeSetup ' if width else '') + 'physical data arithmetic\n'
          '  rw [clock_lookup_inventory]\n')
    timestamps = [f'clean_timestamp_lookup {o["args"]}.timestampExpression{i} {environment} ({o["args"]}.timestamp_bound{i} physical data arithmetic helpers)'
                  for i in range(len(pair['circuit']['timestamp_range_check_lookup_expressions']))]
    proofs = range_proofs + (timestamps[alignment_start:] if worker else []) + [proof for _, proof in sorted(generic_proofs)] + timestamps
    tree = 'PredicateChecks.nil'
    for proof in reversed(proofs):
        tree = f'(PredicateChecks.cons ({proof}) {tree})'
    s += f'  exact PredicateChecks.all {tree}\n\nend {namespace}\n'
    return 'GKRProtocol.CleanClosedNative.' + case, s


def modules(name, case, model_name, width):
    target, text = module(name, case, model_name, width)
    generic_blocks = list(re.finditer(r"^theorem generic_lookup[0-9]+\n", text, re.M))
    if len(generic_blocks) <= 8:
        yield target, text
        return
    boundary = text.index('theorem retained_clock_from_source')
    range_start = text.index('theorem range_lookup') if 'theorem range_lookup' in text else generic_blocks[0].start()
    namespace = 'Airbender.Compiler.CleanClosedNative.' + case
    end = '\nend ' + namespace + '\n'
    shared = 'GKRProtocol.CleanClosedParts.' + case + '.Shared'
    yield shared, text[:range_start] + end
    parts = []
    header = (f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
              'set_option warningAsError true\nset_option Elab.async false\n'
              'set_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n')
    for start in range(0, len(generic_blocks), 8):
        part = 'GKRProtocol.CleanClosedParts.' + case + '.Part' + str(start // 8)
        parts.append(part)
        finish = min(start + 8, len(generic_blocks))
        stop = generic_blocks[finish].start() if finish < len(generic_blocks) else boundary
        yield part, 'import ' + shared + '\n\n' + header + text[generic_blocks[start].start():stop] + end
    yield target, (''.join('import ' + part + '\n' for part in parts) + '\n' + header +
                   text[range_start:generic_blocks[0].start()] + text[boundary:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    unsupported = set(args.family or []) & {'jump-branch', 'mul-div', 'shift-binop'}
    if unsupported:
        parser.error('fixed-table adapters remain open: ' + ', '.join(sorted(unsupported)))
    for family, stem, model, width in zip(FAMILIES, CASES, MODELS, WIDTHS, strict=True):
        if args.family and family not in args.family:
            continue
        if not width and family != 'add-sub':
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            for target, text in modules(family + '-' + mode, stem + mode.title(), model, width):
                path = LEAN / (target.replace('.', '/') + '.lean')
                if args.check and (not path.exists() or path.read_text() != text):
                    raise ValueError('retained lookup closure changed: ' + target)
                if args.write and (not path.exists() or path.read_text() != text):
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(text)
                print(target, flush=True)
                if args.build:
                    subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                                   env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
