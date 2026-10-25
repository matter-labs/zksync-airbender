#!/usr/bin/env python3
"""Bind source query and setup values to outputs of whole native graph witnesses."""
import argparse
import json
import os
import re
import subprocess
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_oracle_frame_instances import module as oracle_module


def module(name, case):
    _, source_text = oracle_module(name, case)
    prefix = 'Airbender.Compiler.'
    owner = {key: prefix + model + '.' + case + '.native' for key, model in [
        ('base', 'FullArithmeticNative'), ('source', 'SourceContractNative'),
        ('helper', 'HelperValidityNative'), ('fields', 'HelperNative'), ('memory', 'MemoryNative'),
        ('counter', 'CounterFrameNative'), ('table', 'TableNative'), ('graph', 'FunctionalNative'),
        ('lookup', 'LookupNative'), ('queries', 'LookupSourceNative'), ('frame', 'QueryFrameNative'),
        ('links', 'FunctionalLinksNative'), ('setup', 'MaterializedNative')]}
    o = owner
    model = o['setup'] + '.model'
    typing = prefix + 'ConsumerNative.' + case + '.native.typing'
    pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
    groups = [kind for kind in pair['circuit']['global_output_map'] if kind in
              ['GenericLookup', 'Lookup16Bits', 'LookupTimestamps']]
    stems = {'GenericLookup': 'generic', 'Lookup16Bits': 'range16', 'LookupTimestamps': 'timestamp'}
    prop_terms = []
    checks = []
    for ordinal, kind in enumerate(groups):
        stem = stems[kind]
        count = f'counts ⟨{ordinal}, by decide⟩'
        if kind == 'LookupTimestamps':
            query_terms = f"{o['fields']}.fields.map (fun field => RationalPair.leaf 1\n      (hom (field.value ({o['base']}.helperPlacement.project ({o['helper']}.canonical sourceValue))) + gamma))"
        else:
            query_terms = f"{o['queries']}.{stem}Queries.map (fun query =>\n      query.value hom challenges.lookupAlpha gamma (sourceValue ∘ {o['base']}.originalProjection))"
        prop_terms.append(f"({o['lookup']}.{stem}Output).value values =\n    (({query_terms}) ++\n      [({model}.row {o['table']}.{stem}SetupColumns row ({count})).value hom challenges.lookupAlpha gamma]).sum")
        checks.append(f"theorem {stem}Columns : {o['table']}.{stem}SetupColumns.all\n    (fun column => decide (column ∈ {prefix}OracleFrameNative.{case}.native.columns)) = true := by decide +kernel\n")
    head = source_text[source_text.index('theorem oracle_graph_extends'):source_text.index(' := by\n', source_text.index('theorem oracle_graph_extends'))]
    head = head.replace('theorem oracle_graph_extends', 'theorem source_outputs_extends')
    head = head.replace('native.columns', prefix + 'OracleFrameNative.' + case + '.native.columns')
    source_binder = head[head.index('    (sourceValue :'):head.index('    (original :')].strip()
    count_binder = f"(counts : Fin {o['table']}.multiplicityColumns.length → Source.BaseField)"
    prop = ('def OutputsPreserved {R : Type} [CommRing R]\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            f'    {source_binder}\n    {count_binder}\n'
            f'    (row : Fin {model}.imported.data.length) (values : GKRAddress → R) : Prop :=\n  ' + '\n  ∧ '.join(prop_terms) + '\n\n')
    body = (f"  obtain ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers⟩ :=\n"
            f"    {prefix}OracleFrameNative.{case}.oracle_graph_extends hom challenges gamma sourceValue original clockValid primitives counts row fallback\n"
            '  refine ⟨baseValue, values, inputAgreement, arithmetic, baseLaw, affine, lookups, products, countsAt, setupAt, helpers, ?_⟩\n'
            '  let assignment : TypedAssignment R := ⟨baseValue, values⟩\n'
            f'  have typedEq : assignment.value {typing} hom = values := TypedAssignment.value_eq assignment {typing} hom baseLaw\n'
            f"  have defined : ∀ definition ∈ {o['queries']}.definitions, definition.Holds hom challenges (assignment.value {typing} hom) := by\n"
            f"    rw [typedEq, ← {o['links']}.lookupDefinitionsAgree]\n    exact affine\n"
            f"  have helperDefined : ∀ definition ∈ {o['fields']}.definitions, definition.Holds hom challenges (assignment.value {typing} hom) := by\n"
            f"    rw [typedEq, ← {o['links']}.helperDefinitionsAgree]\n    exact affine\n"
            f"  have holds : ∀ gate ∈ {o['lookup']}.gates, gate.Holds hom challenges gamma (assignment.value {typing} hom) := by\n"
            '    rw [typedEq]\n    exact lookups\n'
            '  unfold OutputsPreserved\n')
    if len(groups) > 1:
        body += '  refine ⟨' + ', '.join('?_ ' for _ in groups[:-1]) + ', ?_⟩\n'
    for ordinal, kind in enumerate(groups):
        stem = stems[kind]
        indent = '  ' if len(groups) == 1 else '  · '
        body += indent + f"have tableCells : ∀ column ∈ {o['table']}.{stem}SetupColumns, assignment.base column.address = {model}.value row column := by\n"
        body += f"      intro column member\n      exact setupAt column (of_decide_eq_true (List.all_eq_true.mp {stem}Columns column member))\n"
        columns = {'GenericLookup': 'multiplicities_columns_for_generic_lookup', 'Lookup16Bits': 'multiplicities_columns_for_range_check_16', 'LookupTimestamps': 'multiplicities_columns_for_timestamp_range_check'}
        column = pair['circuit']['witness_layout'][columns[kind]]['start']
        body += f"    have countCell : assignment.base (.BaseLayerWitness {column}) = counts ⟨{ordinal}, by decide⟩ := countsAt ⟨{ordinal}, by decide⟩\n"
        if kind == 'LookupTimestamps':
            # Timestamp reduction includes compiler-created scalar helper queries.
            body += f"    have reduced := {o['fields']}.timestampSourceReduction hom challenges gamma assignment helperDefined\n"
            body += f"      ({o['links']}.helperCopies baseValue arithmetic) holds\n"
            body += f"    change ({o['lookup']}.timestampOutput).value (assignment.value {typing} hom) =\n"
            helper_source = (LEAN / 'GKRProtocol/HelperNative' / (case + '.lean')).read_text()
            cert = json.loads(json.loads(re.search(r'selectors ("(?:[^"\\]|\\.)*")', helper_source).group(1)))
            setup_leaf = cert['setup_leaf']
            body += f"      ({o['fields']}.fields.map (fun field => RationalPair.leaf 1 (hom (field.value ({o['fields']}.sourceValues baseValue)) + gamma)) ++\n"
            body += f"        [NativeLookupLeaf.registryValue {o['lookup']}.registry hom challenges gamma (assignment.value {typing} hom) {setup_leaf}]).sum at reduced\n"
            body += f"    rw [{o['table']}.timestampSetupInterpreted hom challenges gamma assignment defined\n      ({model}.value row) (counts ⟨{ordinal}, by decide⟩) tableCells countCell, typedEq] at reduced\n"
            body += '    apply reduced.trans\n    congr 2\n    apply List.map_congr_left\n    intro field member\n'
            body += f"    have same := Source.HelperField.transport_value field {o['base']}.helperPlacement {o['fields']}.placement\n"
            body += f"      {o['base']}.inputBank {o['memory']}.bank (List.all_eq_true.mp {o['helper']}.transportChecked field member)\n"
            body += f"      ({o['counter']}.assigned ({o['helper']}.canonical sourceValue) counts) baseValue inputAgreement\n"
            body += f"    change field.value ({o['fields']}.sourceValues baseValue) = _ at same\n"
            body += f"    rw [same, {o['counter']}.helpers_preserved ({o['helper']}.canonical sourceValue) counts field member]\n"
        else:
            body += f"    have reduced := {o['table']}.{stem}SourceTableReduction hom challenges gamma assignment defined\n"
            body += f"      ({o['links']}.lookupCopies baseValue arithmetic) holds ({model}.value row) (counts ⟨{ordinal}, by decide⟩) tableCells countCell\n"
            body += f"    rw [typedEq] at reduced\n    apply reduced.trans\n    congr 2\n    apply List.map_congr_left\n    intro query member\n"
            body += f"    apply {o['frame']}.queries_preserved hom challenges.lookupAlpha gamma sourceValue counts baseValue inputAgreement query\n"
            query_groups = [group for group in groups if group != 'LookupTimestamps']
            if len(query_groups) > 1:
                body += f"    simp only [{o['frame']}.queries, List.mem_append]\n"
            branch = 'member' if len(query_groups) == 1 else ('Or.inl member' if query_groups.index(kind) == 0 else 'Or.inr member')
            body += '    exact ' + branch + '\n'
    target = 'GKRProtocol.MaterializedWitnessNative.' + case
    content = (f'import GKRProtocol.NativeWitness\nimport GKRProtocol.OracleFrameNative.{case}\n'
               f'import GKRProtocol.QueryFrameNative.{case}\nimport GKRProtocol.FunctionalLinksNative.{case}\n'
               f'import GKRProtocol.MaterializedRangeNative.{case}\nimport GKRProtocol.GroupedTrace\n\n'
               f'namespace Airbender.Compiler.MaterializedWitnessNative.{case}\nopen Airbender Airbender.Compiler\n'
               'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n' +
               '\n'.join(checks) + '\n' + prop + head + ' ∧\n      OutputsPreserved hom challenges gamma sourceValue counts row values := by\n' + body +
               trace_layer(case, o, groups, model, typing, source_binder, head) +
               f'\nend Airbender.Compiler.MaterializedWitnessNative.{case}\n')
    return target, content


def trace_layer(case, o, groups, model, typing, source_binder, head):
    stems = {'GenericLookup': 'generic', 'Lookup16Bits': 'range16', 'LookupTimestamps': 'timestamp'}
    size = len(groups)
    scalar = f"{o['fields']}.fields.map (fun field => MaterializedQuery.mk\n      [field.value ({o['base']}.helperPlacement.project ({o['helper']}.canonical sourceValue))] 1)"
    requests = []
    valid = []
    for kind in groups:
        stem = stems[kind]
        if kind == 'LookupTimestamps':
            requests.append(scalar)
        else:
            requests.append(f"{o['queries']}.{stem}Queries.map (fun query => query.materialized (sourceValue ∘ {o['base']}.originalProjection))")
            valid.append(f"∀ query ∈ {o['queries']}.{stem}Queries,\n    query.weight (RingHom.id _) (sourceValue ∘ {o['base']}.originalProjection) ≠ 0 →\n    {model}.Contains {o['table']}.{stem}SetupColumns\n      (query.fields.map (fun field => field.value (sourceValue ∘ {o['base']}.originalProjection)))")
    out = f"\nnoncomputable def outputPorts (group : Fin {size}) : RationalPorts :=\n  ([" + ', '.join(o['lookup'] + '.' + stems[k] + 'Output' for k in groups) + "]).get group\n\n"
    out += f"def setupColumns (group : Fin {size}) : List SourceSetupColumn :=\n  ([" + ', '.join(o['table'] + '.' + stems[k] + 'SetupColumns' for k in groups) + "]).get group\n\n"
    out += f"noncomputable def sourceRequests {source_binder} (group : Fin {size}) : List MaterializedQuery :=\n  ([" + ',\n    '.join(requests) + "]).get group\n\n"
    out += f"def AuthoredLookupValid {source_binder} : Prop :=\n  " + ('\n  ∧ '.join('(' + condition + ')' for condition in valid) or 'True') + '\n\n'
    count_binder = f"(counts : Fin {size} → Source.BaseField)"
    out += ('theorem outputs_preserved_uniform {R : Type} [CommRing R]\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            f'    {source_binder}\n    {count_binder}\n'
            f'    (row : Fin {model}.imported.data.length) (values : GKRAddress → R)\n'
            '    (preserved : OutputsPreserved hom challenges gamma sourceValue counts row values) :\n'
            f'    ∀ group : Fin {size}, (outputPorts group).value values =\n'
            '      (((sourceRequests sourceValue group).map (fun query => query.value hom challenges.lookupAlpha gamma)) ++\n'
            f'        [({model}.row (setupColumns group) row (counts group)).value hom challenges.lookupAlpha gamma]).sum := by\n'
            '  intro group\n  fin_cases group\n')
    for index, kind in enumerate(groups):
        projection = 'preserved' if size == 1 else 'preserved' + '.2' * index + ('.1' if index < size - 1 else '')
        out += ('  · convert ' + projection + ' using 1 <;> simp [outputPorts, sourceRequests, setupColumns, List.map_map, Function.comp_def]\n'
                f'    have coordinate : ({index} : Fin {size}) = (⟨{index}, by decide⟩ : Fin {o["table"]}.multiplicityColumns.length) := by decide +kernel\n'
                '    rw [coordinate]\n')
    out += (f'\ntheorem source_requests_valid {source_binder}\n'
            f"    (primitives : {o['helper']}.profile.ExecutionValid ({o['helper']}.execute.value ({o['base']}.helperPlacement.memory.project sourceValue))\n"
            f"      ({o['base']}.helperPlacement.memory.project sourceValue))\n"
            '    (authored : AuthoredLookupValid sourceValue) :\n'
            f'    ∀ group : Fin {size}, ∀ query ∈ sourceRequests sourceValue group, query.weight ≠ 0 →\n'
            f'      {model}.Contains (setupColumns group) query.fields := by\n'
            '  intro group\n  fin_cases group\n')
    authored_groups = [kind for kind in groups if kind != 'LookupTimestamps']
    for index, kind in enumerate(groups):
        out += f'  · intro query member nonzero\n    change query ∈ ({requests[index]}) at member\n'
        out += '    obtain ⟨item, included, same⟩ := List.mem_map.mp member\n    rw [← same] at nonzero ⊢\n'
        if kind == 'LookupTimestamps':
            out += f"    exact Airbender.Compiler.MaterializedRangeNative.{case}.native.timestamp_contains _\n      ({o['helper']}.helper_membership sourceValue primitives item included)\n"
        else:
            ordinal = authored_groups.index(kind)
            projection = 'authored' if len(authored_groups) == 1 else 'authored' + '.2' * ordinal + ('.1' if ordinal < len(authored_groups) - 1 else '')
            out += f'    exact {projection} item included nonzero\n'
    row_prop = head[head.index('      (∀ wire'):]
    out += ('\ndef RowWitness {R : Type} [CommRing R]\n'
            '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)\n'
            f'    {source_binder}\n    {count_binder}\n'
            f'    (row : Fin {model}.imported.data.length) (baseValue : GKRAddress → Source.BaseField)\n'
            '    (values : GKRAddress → R) : Prop :=\n' + row_prop +
            ' ∧\n      OutputsPreserved hom challenges gamma sourceValue counts row values\n\n')
    trace_binder = source_binder.replace('(sourceValue : ', f'(sourceValue : Fin {model}.imported.data.length → ')
    source_at = 'sourceValue row'
    out += ('theorem native_lookup_trace_extends\n'
            f'    {trace_binder}\n'
            f"    (original : ∀ row, Satisfies ({o['source']}.originals.map Expression.polynomial) (sourceValue row))\n"
            f"    (clockValid : ∀ row, Source.clockContract {o['source']}.clock ({o['base']}.helperPlacement.memory.project (sourceValue row)))\n"
            f"    (primitives : ∀ row, {o['helper']}.profile.ExecutionValid ({o['helper']}.execute.value ({o['base']}.helperPlacement.memory.project (sourceValue row)))\n"
            f"      ({o['base']}.helperPlacement.memory.project (sourceValue row)))\n"
            '    (authored : ∀ row, AuthoredLookupValid (sourceValue row))\n'
            f'    (fallback : Fin {model}.imported.data.length → GKRAddress → Source.BaseField) :\n'
            f'    ∃ counts : Fin {model}.imported.data.length → Fin {size} → Source.BaseField,\n'
            '      ∀ {R : Type} [CommRing R] (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R),\n'
            f'      ∃ baseValue : Fin {model}.imported.data.length → GKRAddress → Source.BaseField,\n'
            f'      ∃ values : Fin {model}.imported.data.length → GKRAddress → R,\n'
            '        (∀ row, RowWitness hom challenges gamma (sourceValue row) (counts row) row (baseValue row) (values row)) ∧\n'
            f'        ∀ group : Fin {size}, ((List.finRange {model}.imported.data.length).map\n'
            '          (fun row => (outputPorts group).value (values row))).sum.numerator = 0 := by\n'
            f'  obtain ⟨counts, cancel⟩ := {model}.grouped_trace_counter_witness setupColumns {o["setup"]}.positive\n'
            '    (fun row => sourceRequests (sourceValue row))\n'
            '    (fun row => source_requests_valid (sourceValue row) (primitives row) (authored row))\n'
            '  refine ⟨counts, ?_⟩\n  intro R _ hom challenges gamma\n  classical\n'
            f'  have complete (row : Fin {model}.imported.data.length) :\n'
            '      ∃ baseValue : GKRAddress → Source.BaseField, ∃ values : GKRAddress → R,\n'
            '      RowWitness hom challenges gamma (sourceValue row) (counts row) row baseValue values :=\n'
            '    source_outputs_extends hom challenges gamma (sourceValue row) (original row) (clockValid row)\n'
            '      (primitives row) (counts row) row (fallback row)\n'
            '  choose baseValue values correct using complete\n'
            '  refine ⟨baseValue, values, correct, ?_⟩\n  intro group\n'
            f'  have same : ((List.finRange {model}.imported.data.length).map (fun row => (outputPorts group).value (values row))) =\n'
            f'      ((List.finRange {model}.imported.data.length).map (fun row =>\n'
            '        (((sourceRequests (sourceValue row) group).map (fun query => query.value hom challenges.lookupAlpha gamma)) ++\n'
            f'          [({model}.row (setupColumns group) row (counts row group)).value hom challenges.lookupAlpha gamma]).sum)) := by\n'
            '    apply List.map_congr_left\n    intro row _\n'
            '    exact outputs_preserved_uniform hom challenges gamma (sourceValue row) (counts row) row (values row)\n'
            '      (correct row).2.2.2.2.2.2.2.2.2 group\n'
            '  rw [same]\n  exact cancel group hom challenges.lookupAlpha gamma\n')
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            name, case = family + '-' + mode, stem + mode.title()
            target, content = module(name, case)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != content):
                raise ValueError('materialized witness scaffold changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != content):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
            print(name, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'],
                               cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
