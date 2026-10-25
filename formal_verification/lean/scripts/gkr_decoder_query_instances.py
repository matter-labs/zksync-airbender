#!/usr/bin/env python3
"""Connect compiled decoder query expressions to actual native setup soundness."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import FAMILIES,LEAN
from gkr_wiring_instances import CASES
from gkr_clean_links import MODELS
from gkr_decoder_tail_instances import SPECS
from gkr_decoder_membership_instances import KINDS
from gkr_lookup_source_certificate import synthesis

SETUP={'unified':('Unified','unifiedSetup','unifiedDecoderData'),
 'add-sub':('AddSub','addSubSetup','addSubDecoderData'),
 'jump-branch':('JumpBranch','jumpBranchSetup','jumpBranchDecoderData'),
 'mul-div':('MulDiv','mulDivSetup','mulDivDecoderData'),
 'shift-binop':('ShiftBinop','shiftBinopSetup','shiftDecoderData'),
 'word-memory':('WordMemory','wordMemorySetup','wordDecoderData'),
 'subword-memory':('Subword','subwordSetup','subwordDecoderData')}


def module(family,stem,model,mode):
    if family not in SETUP:return None
    case=stem+mode.title();data_module,setup,prefix=SETUP[family]
    pair=json.loads((LEAN/f'artifacts/compiler/{family}-{mode}.json').read_text())
    certificate=json.loads((LEAN/f'artifacts/compiler/lookup/{family}-{mode}.json').read_text())
    rows=[r for r in certificate['rows'] if r['kind']=='decoder'];assert len(rows)==1
    selector=[entry for entry in synthesis(pair,certificate)['operands'] if entry['kind']=='decoder'];assert len(selector)==1
    source_query=f'Airbender.Compiler.LookupSourceNative.{case}.native.query{selector[0]["native_leaf"]}'
    source_bank=f'Airbender.Compiler.LookupSourceNative.{case}.native.bank'
    source_place=f'Airbender.Compiler.LookupNative.{case}.native.sourcePlacement'
    generic_rows=[r for r in certificate['rows'] if r['kind'] in ['generic','decoder']]
    query_index=next(i for i,r in enumerate(generic_rows) if r['kind']=='decoder')
    generic_queries=f'Airbender.Compiler.LookupSourceNative.{case}.native.genericQueries'
    query_frame=f'Airbender.Compiler.QueryFrameNative.{case}.native'
    assigned=f'Airbender.Compiler.CounterFrameNative.{case}.native.assigned'
    canonical=f'Airbender.Compiler.HelperValidityNative.{case}.native.canonical'
    authored=f'Airbender.Compiler.MaterializedWitnessNative.{case}.AuthoredLookupValid'
    base=f'Airbender.Compiler.FullArithmeticNative.{case}.native'
    model_data=f'Airbender.Compiler.MaterializedNative.{case}.native.model'
    table=f'Airbender.Compiler.TableNative.{case}.native'
    width=len(rows[0]['fields'])-1
    args=f'Airbender.Compiler.DecoderArgumentsNative.{case}.native';clean=f'Airbender.Compiler.CleanArithmeticNative.{case}.native'
    trace=f'Airbender.{model}.importedConstraintsTraceColumns';decoder=f'Airbender.{model}.importedConstraintsDecoderColumns'
    member=f'Airbender.Compiler.DecoderTail.{stem}.Membership'
    name='GKRProtocol.DecoderQueryNative.'+case;owner='Airbender.Compiler.DecoderQueryNative.'+case
    text=f'import GKRProtocol.DecoderQueryFrame\nimport GKRProtocol.MaterializedWitnessNative.{case}\nimport GKRProtocol.CleanGenericSetup\nimport GKRProtocol.MaterializedNative.{case}\nimport GKRProtocol.PackedDecoderNormalization\nimport GKRProtocol.DecoderArgumentsNative.{case}\nimport GKRProtocol.DecoderTail.{stem}.Membership\n\nnamespace {owner}\nopen Airbender Airbender.Compiler Airbender.Trace.NativeDecoder\n'
    text+='set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    text+=f'noncomputable def expressions : Vector (_root_.Expression Source.BaseField) {width} :=\n  #v['+', '.join(f'{args}.expression{i}' for i in range(1,width+1))+']\n\n'
    text+=f'theorem payload_inventory : expressions.toList = {args}.payloadExpressions := by rfl\n\n'
    text+=f'noncomputable def values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n    Vector Source.BaseField {width} := expressions.map (fun expression => expression.eval ({clean}.environment physical data))\n\n'
    text+=f'theorem normalization_geometry (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n    normalizeDecoderFields {setup} (values physical data) =\n      activeQuery ((decoderExpressions {trace} {decoder}).map\n        (fun expression => expression.eval ({clean}.environment physical data))) := by\n  apply Vector.ext\n  intro column bound\n  interval_cases column <;>\n    simp [normalizeDecoderFields, values, expressions, activeQuery, _root_.Expression.eval,\n      {setup}, {prefix}ColumnsMask, {prefix}Tagged,\n      '+', '.join(f'{args}.expression{i}' for i in range(1,width+1))+']\n\n'
    if width<10:text=text.replace('expressions, activeQuery, _root_.Expression.eval,','expressions, activeQuery, decoderExpressions, _root_.Expression.eval,\n      '+trace+', '+decoder+',')
    text+=f'theorem normalized_values (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n    normalizeDecoderFields {setup} (values physical data) =\n      activeQuery (Trace.nativeDecoderQuery {trace} {decoder}\n        (fun index => ({clean}.environment physical data).get index)) :=\n  (normalization_geometry physical data).trans\n    (congrArg activeQuery (decoder_expressions_value {trace} {decoder} ({clean}.environment physical data)))\n\n'
    text+=f'theorem source_payload (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n    (arithmetic : ∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (physical ∘ {base}.bank.address) = 0) :\n    (values physical data).toList = {source_query}.fields.map (fun field => field.value ((physical ∘ {source_bank}.address) ∘ {source_place})) := by\n  rw [values, Vector.toList_map, payload_inventory]\n  exact {args}.payload_fields physical data arithmetic\n\n'
    text+=f'theorem program_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)\n    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n    (typed : (({clean}.environment physical data).get {trace}.initialPC[0]).val < 65536)\n    (present : ({member}.nativeSetup.imported.data.table "Airbender.Native.{model}").Contains #[] (values physical data)) :\n    (Trace.decoderTable {"unifiedProgram .machine" if family=="unified" else "pooledProgram ."+KINDS[family]}).Contains #[]\n      (Trace.nativeDecoderQuery {trace} {decoder} (fun index => ({clean}.environment physical data).get index)) := by\n'
    if family=='unified':
        text+='  have identity := Airbender.Compiler.DecoderTail.Unified.Rows.normalize_fields_identity (values physical data)\n'
        text+='  have same := identity.symm.trans (normalized_values physical data)\n  rw [same] at present\n'
        text+=f'  exact {member}.lookup_sound capacity _ typed present\n'
    else:text+=f'  exact {member}.lookup_sound capacity (values physical data) _ typed (normalized_values physical data) present\n'
    text+=f'\ntheorem program_from_source_membership (capacity : FieldCapacity.NoWrap babyBearModulus 65536)\n    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n    (arithmetic : ∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (physical ∘ {base}.bank.address) = 0)\n    (typed : (({clean}.environment physical data).get {trace}.initialPC[0]).val < 65536)\n    (member : {model_data}.Contains {table}.genericSetupColumns\n      ({source_query}.fields.map (fun field => field.value ((physical ∘ {source_bank}.address) ∘ {source_place})))) :\n    (Trace.decoderTable {"unifiedProgram .machine" if family=="unified" else "pooledProgram ."+KINDS[family]}).Contains #[]\n      (Trace.nativeDecoderQuery {trace} {decoder} (fun index => ({clean}.environment physical data).get index)) := by\n'
    text+=f'  have columns : {table}.genericSetupColumns = (List.range {width}).map SourceSetupColumn.generic := by decide +kernel\n'
    text+='  have payload := source_payload physical data arithmetic\n  rw [← payload] at member\n'
    text+=f'  have present := {model_data}.generic_clean_contains {table}.genericSetupColumns columns (values physical data) member "Airbender.Native.{model}" #[]\n'
    text+='  exact program_membership capacity physical data typed present\n'
    text+=f'\ntheorem decoder_query_member : {source_query} ∈ {generic_queries} := by\n  have same : {generic_queries}.get ⟨{query_index}, by decide⟩ = {source_query} := by rfl\n  exact same ▸ List.get_mem {generic_queries} ⟨{query_index}, by decide⟩\n\n'
    text+=f'theorem program_from_framed_source (capacity : FieldCapacity.NoWrap babyBearModulus 65536)\n    (sourceValue : Fin {base}.inputs.length → Source.BaseField) (counts : Fin {table}.multiplicityColumns.length → Source.BaseField)\n    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)\n    (inputAgreement : ∀ wire, physical ({base}.inputBank.address wire) = {assigned} ({canonical} sourceValue) counts wire)\n    (arithmetic : ∀ gate ∈ {base}.artifact.gates, gate.expressionResidual (physical ∘ {base}.bank.address) = 0)\n    (typed : (({clean}.environment physical data).get {trace}.initialPC[0]).val < 65536)\n    (enabled : ({args}.expression0).eval ({clean}.environment physical data) ≠ 0)\n    (valid : {authored} sourceValue) :\n    (Trace.decoderTable {"unifiedProgram .machine" if family=="unified" else "pooledProgram ."+KINDS[family]}).Contains #[]\n      (Trace.nativeDecoderQuery {trace} {decoder} (fun index => ({clean}.environment physical data).get index)) := by\n'
    text+=f'  have framed : ∀ field ∈ {source_query}.usedFields, field.value ((physical ∘ {source_bank}.address) ∘ {source_place}) = field.value (sourceValue ∘ {base}.originalProjection) := by\n    intro field included\n    apply {query_frame}.fields_preserved sourceValue counts physical inputAgreement field\n    exact List.mem_flatMap.mpr ⟨{source_query}, List.mem_append_left _ decoder_query_member, included⟩\n'
    text+=f'  have weight := decoder_weight_congr {source_query} _ _ framed\n  rw [{args}.execute_weight physical data arithmetic] at weight\n  have nonzero : {source_query}.weight (RingHom.id _) (sourceValue ∘ {base}.originalProjection) ≠ 0 := by\n    rw [← weight]\n    exact enabled\n'
    text+='  have present := valid.1 _ decoder_query_member nonzero\n'
    text+=f'  have payload := decoder_fields_congr {source_query} _ _ framed\n  have moved := (congrArg (fun fields => {model_data}.Contains {table}.genericSetupColumns fields) payload).mpr present\n  exact program_from_source_membership capacity physical data arithmetic typed moved\n'
    return name,text+'\nend '+owner+'\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--family',choices=SETUP,action='append');parser.add_argument('--mode',choices=['uncached','cached'],action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for family,stem,model in zip(FAMILIES,CASES,MODELS,strict=True):
        if args.family and family not in args.family:continue
        for mode in args.mode or ['uncached','cached']:
            generated=module(family,stem,model,mode)
            if generated is None:continue
            name,text=generated;path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('decoder query scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
