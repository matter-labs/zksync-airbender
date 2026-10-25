#!/usr/bin/env python3
"""Identify actual source executor RAM/PC rows with retained logical tokens."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES
from gkr_clean_links import MODELS


def module(name, case, model):
    namespace = 'Airbender.Compiler.MemoryPortsNative.' + case
    memory = 'Airbender.Compiler.MemoryNative.' + case + '.native'
    artifact = 'Airbender.' + model + '.importedConstraints'
    full = 'Airbender.Compiler.FullArithmeticNative.' + case + '.native'
    clean = 'Airbender.Compiler.CleanArithmeticNative.' + case + '.native'
    pair = json.loads((LEAN / 'artifacts/compiler' / (name + '.json')).read_text())
    source_count = pair['source']['num_variables']
    text = (f'import GKRProtocol.CleanArithmeticNative.{case}\n'
            f'import GKRProtocol.MemoryTokens\nimport GKRProtocol.MemoryNative.{case}\n'
            f'import GKRProtocol.FunctionalLinksNative.{case}\nimport GKRProtocol.NativeWitness\n'
            f'import Airbender.Review.Circuits.{model}.Artifact\n\n'
            f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
            'set_option warningAsError true\nset_option Elab.async false\n'
            'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n')
    for direction, point in [('read', 'initial'), ('write', 'final')]:
        token = ('Trace.readToken assignment' if direction == 'read' else
                 f'Trace.writeToken {artifact}TraceColumns assignment')
        proof = 'rfl'
        if model in ['WordMemory', 'SubwordMemory', 'UnifiedReduced']:
            definitions = [memory + '.memory' + direction.title() + 'Rows', artifact + 'MemoryPorts',
                artifact + 'TraceColumns', 'Source.MemoryRow.token', 'Source.MemoryField.value',
                'Source.LookupInput.value', 'Trace.' + direction + 'Token', 'Trace.rawPair',
                'Trace.MemoryPort.' + direction + 'Code', 'Trace.WordColumns.code',
                'Trace.WordColumns.evaluate', 'Trace.pairCode', 'Trace.MemoryAddress.code', 'pcStateMemoryToken', 'sub_eq_add_neg']
            if model == 'UnifiedReduced':
                definitions.remove('sub_eq_add_neg')
            proof = 'simp [' + ', '.join(definitions) + ']'
        text += (f'theorem source_{direction}_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :\n'
                 f'    ({memory}.memory{direction.title()}Rows.map (fun row => row.token {{other with original := assignment}})) =\n'
                 f'      {artifact}MemoryPorts.toList.map ({token}) ++\n'
                 f'        [pcStateMemoryToken ⟨Trace.rawPair assignment {artifact}TraceColumns.{point}PC,\n'
                 f'          Trace.rawPair assignment {artifact}TraceColumns.{point}Time⟩] := by\n  {proof}\n\n')
    text += (f'theorem original_columns : (List.range {source_count}).all (fun index =>\n'
             f'    decide ({full}.bank.address ({clean}.placement index) =\n'
             f'      {memory}.bank.address ({memory}.sourcePlacement.original index))) = true := by decide +kernel\n\n'
             f'theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n'
             f'    (index : Nat) (bounded : index < {source_count}) :\n'
             f'    ({clean}.environment physical data).get index = ({memory}.sourceValues physical).original index := by\n'
             '  exact congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index (List.mem_range.mpr bounded)))\n\n')
    for direction in ['read', 'write']:
        rows = memory + '.memory' + direction.title() + 'Rows'
        text += (f'theorem {direction}_original_indices : {rows}.all\n'
                 f'    (fun row => row.originalIndices.all (fun index => decide (index < {source_count}))) = true := by decide +kernel\n\n'
                 f'theorem {direction}_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n'
                 f'    {rows}.map (fun row => row.token ({memory}.sourceValues physical)) =\n')
        point = 'initial' if direction == 'read' else 'final'
        token = (f'Trace.readToken ({clean}.environment physical data).get' if direction == 'read' else
                 f'Trace.writeToken {artifact}TraceColumns ({clean}.environment physical data).get')
        text += (f'      {artifact}MemoryPorts.toList.map ({token}) ++\n'
                 f'        [pcStateMemoryToken ⟨Trace.rawPair ({clean}.environment physical data).get {artifact}TraceColumns.{point}PC,\n'
                 f'          Trace.rawPair ({clean}.environment physical data).get {artifact}TraceColumns.{point}Time⟩] := by\n'
                 f'  rw [← source_{direction}_tokens ({clean}.environment physical data).get ({memory}.sourceValues physical)]\n'
                 '  apply List.map_congr_left\n  intro row member\n  apply Source.MemoryRow.token_congr\n'
                 '  intro field included\n  apply Eq.symm\n  apply Source.MemoryField.withOriginal_value\n'
                 '  intro index used\n  apply original_assignment\n'
                 f'  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp {direction}_original_indices row member) index\n'
                 '    (List.mem_flatMap.mpr ⟨field, included, used⟩))\n\n')
    for direction in ['read', 'write']:
        rows = memory + '.memory' + direction.title() + 'Rows'
        point = 'initial' if direction == 'read' else 'final'
        token = (f'Trace.readToken ({clean}.environment physical data).get' if direction == 'read' else
                 f'Trace.writeToken {artifact}TraceColumns ({clean}.environment physical data).get')
        text += (f'theorem {direction}_products_from_base {{R : Type}} [CommRing R]\n'
                 '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
                 '    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n'
                 f'    ({rows}.map (fun row => row.fingerprint ({memory}.sourceValues physical) hom challenges)).prod =\n'
                 f'      (({artifact}MemoryPorts.toList.map ({token}) ++\n'
                 f'        [pcStateMemoryToken ⟨Trace.rawPair ({clean}.environment physical data).get {artifact}TraceColumns.{point}PC,\n'
                 f'          Trace.rawPair ({clean}.environment physical data).get {artifact}TraceColumns.{point}Time⟩]).map\n'
                 '        (memoryTokenFingerprint hom challenges)).prod := by\n'
                 f'  rw [← Source.MemoryRow.token_products {rows} ({memory}.sourceValues physical) hom challenges,\n'
                 f'    {direction}_tokens_from_base physical data]\n\n')
    graph = 'Airbender.Compiler.FunctionalNative.' + case + '.native'
    links = 'Airbender.Compiler.FunctionalLinksNative.' + case + '.native'
    product = 'Airbender.Compiler.ProductNative.' + case + '.native'
    typing = 'Airbender.Compiler.ConsumerNative.' + case + '.native.typing'
    snapshot = json.loads((LEAN / 'artifacts/compiler' / (name + '-source.json')).read_text())
    execute_index = snapshot['semantic_inputs']['executor_machine_state']['execute']
    for direction in ['read', 'write']:
        rows = memory + '.memory' + direction.title() + 'Rows'
        point = 'initial' if direction == 'read' else 'final'
        token = (f'Trace.readToken ({clean}.environment physical data).get' if direction == 'read' else
                 f'Trace.writeToken {artifact}TraceColumns ({clean}.environment physical data).get')
        native_stem = memory + '.memory' + direction.title()
        text += (f'theorem {direction}_output_logical {{R : Type}} [CommRing R]\n'
                 '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
                 '    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n'
                 '    (values : GKRAddress → R)\n'
                 f'    (baseLaw : ∀ address, {graph}.isBase address = true → values address = hom (physical address))\n'
                 f'    (arithmetic : ∀ gate ∈ {full}.artifact.gates, gate.expressionResidual (physical ∘ {full}.bank.address) = 0)\n'
                 f'    (affine : ∀ definition ∈ {graph}.definitions, definition.Holds hom challenges values)\n'
                 f'    (products : ∀ gate ∈ {product}.gates, gate.Holds hom challenges values) :\n'
                 f'    values {native_stem}Output =\n'
                 f'      maskProduct (hom (({clean}.environment physical data).get {artifact}TraceColumns.execute))\n'
                 f'      (({artifact}MemoryPorts.toList.map ({token}) ++\n'
                 f'        [pcStateMemoryToken ⟨Trace.rawPair ({clean}.environment physical data).get {artifact}TraceColumns.{point}PC,\n'
                 f'          Trace.rawPair ({clean}.environment physical data).get {artifact}TraceColumns.{point}Time⟩]).map\n'
                 '        (memoryTokenFingerprint hom challenges)).prod := by\n'
                 '  let assignment : TypedAssignment R := ⟨physical, values⟩\n'
                 f'  have typedEq : assignment.value {typing} hom = values := TypedAssignment.value_eq assignment {typing} hom baseLaw\n'
                 f'  have defined : ∀ definition ∈ {memory}.definitions, definition.Holds hom challenges (assignment.value {typing} hom) := by\n'
                 f'    rw [typedEq, ← {links}.memoryDefinitionsAgree]\n'
                 '    exact affine\n'
                 '  have holds := products\n  rw [← typedEq] at holds\n'
                 f'  have reduced := {native_stem}SourceReduction hom challenges assignment defined ({links}.memoryCopies physical arithmetic) holds\n'
                 '  rw [typedEq] at reduced\n'
                 f'  change values {native_stem}Output = maskProduct (hom ({memory}.sourceExecute.value ({memory}.sourceValues physical)))\n'
                 f'    ({rows}.map (fun row => row.fingerprint ({memory}.sourceValues physical) hom challenges)).prod at reduced\n'
                 f'  have executeSame : {memory}.sourceExecute.value ({memory}.sourceValues physical) =\n'
                 f'      ({clean}.environment physical data).get {artifact}TraceColumns.execute :=\n'
                 f'    (original_assignment physical data {execute_index} (by decide +kernel)).symm\n'
                 f'  rw [executeSame, {direction}_products_from_base hom challenges physical data] at reduced\n'
                 '  exact reduced\n\n')
    text += f'end {namespace}\n'
    return 'GKRProtocol.MemoryPortsNative.' + case, text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES[:7], action='append')
    parser.add_argument('--mode', choices=['cached', 'uncached'], action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, stem, model in zip(FAMILIES[:7], CASES[:7], MODELS[:7], strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ['uncached', 'cached']:
            if args.mode and mode not in args.mode:
                continue
            target, text = module(family + '-' + mode, stem + mode.title(), model)
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('source memory token binding changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(target, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
