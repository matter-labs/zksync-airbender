#!/usr/bin/env python3
"""Compose literal full native decoder rows with retained decoder soundness."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_decoder_tail_instances import SPECS
from gkr_rom_columns import length

KINDS={'add-sub':'addSub','jump-branch':'jumpBranchSlt','mul-div':'mulDiv','shift-binop':'shiftBinop','word-memory':'wordMemory','subword-memory':'subwordMemory'}
MODELS={'jump-branch':'JumpBranchSlt'}


def module(family):
    case,data_module,setup,_=SPECS[family];kind=KINDS[family]
    data=json.loads((LEAN/f'artifacts/setup/{family}.json').read_text());width=len(data['columns']);offset=data['circuit']['offset_for_decoder_table'];total=data['trace_len'];tail=total-offset
    owner=f'Airbender.Compiler.DecoderTail.{case}.Membership';target=f'GKRProtocol.DecoderTail.{case}.Membership'
    text=f'import GKRProtocol.DecoderTail.{case}.Rows\nimport GKRProtocol.DecoderSetupRefinement\nimport Airbender.Proofs.Tables.Decoder.{data_module}\n\nnamespace {owner}\nopen Airbender Airbender.Compiler Airbender.Trace.NativeDecoder\n'
    text+='set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\nabbrev nativeSetup := Rows.nativeSetup\n\n'
    if offset:
        blocks=data['columns'][-1]['blocks'];stop=0;size=0
        while size<offset:size+=length(blocks[stop]);stop+=1
        if size!=offset:raise ValueError('tag boundary needs explicit span proof')
        col=f'Data.GKRSetup.{case}.setupColumn{width-1}'
        text+=f'column_blocks_part tagBack from {col} start {stop} stop {len(blocks)}\n\n'
        text+=f'theorem tag_shape : {col}.blocks.toList = {setup}.prefixTags.blocks.toList ++ tagBack := by rfl\n\n'
        text+=f'theorem prefix_tag_length : ({setup}.prefixTags.blocks.toList.map Setup.Block.length).sum = {offset} := by decide +kernel\n\n'
        text+=f'theorem prefix_tag (index : Fin {offset}) : {col}.get? index.val = {setup}.prefixTags.get? index.val := by\n  change Setup.getFromBlocks {col}.blocks.toList index.val = _\n  rw [tag_shape]\n  exact getFromBlocks_before_suffix _ tagBack index.val (by rw [prefix_tag_length]; exact index.isLt)\n\n'
    text+=f'theorem leading_rows (row : Fin {total}) (leading : row.val < {setup}.offset) :\n    {setup}.tagged = true ∧ (normalizeDecoderFields {setup} (Rows.nativeRow row))[9] =\n      (Setup.signedValue (({setup}.prefixTags.get? row.val).getD 0) : Source.BaseField) := by\n'
    if not offset:text+='  have impossible : row.val < 0 := leading\n  omega\n\n'
    else:
        tagged={'JumpBranch':'jumpBranchDecoderDataTagged','MulDiv':'mulDivDecoderDataTagged','ShiftBinop':'shiftDecoderDataTagged','WordMemory':'wordDecoderDataTagged','SubwordMemory':'subwordDecoderDataTagged'}[case]
        text+=f'  refine ⟨by rfl, ?_⟩\n  have same := prefix_tag ⟨row.val, leading⟩\n  have last : (Rows.nativeRow row)[{width-1}] = (Setup.signedValue (({setup}.prefixTags.get? row.val).getD 0) : Source.BaseField) := by\n'
        text+='    simp only [Rows.nativeRow, Setup.TableData.row, Vector.getElem_map, show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n'
        text+=f'    change (Setup.signedValue ((Data.GKRSetup.{case}.setupColumn{width-1}.get? row.val).getD 0) : Source.BaseField) = _\n'
        text+='    exact congrArg (fun value : Option Nat => (Setup.signedValue (value.getD 0) : Source.BaseField)) same\n'
        text+=f'  simpa [normalizeDecoderFields, {setup}, {tagged}] using last\n\n'
    text+=f'theorem tail_rows (row : Fin {total}) (outside : ¬row.val < {setup}.offset) :\n    normalizeDecoderFields {setup} (Rows.nativeRow row) =\n      ({setup}.row ⟨row.val - {setup}.offset, by have := row.isLt; change row.val - {offset} < {tail}; change ¬row.val < {offset} at outside; omega⟩).map\n        (fun n => (Setup.signedValue n : Source.BaseField)) := by\n'
    text+=f'  have lower : {offset} ≤ row.val := by change ¬row.val < {offset} at outside; omega\n  let index : Fin {tail} := ⟨row.val - {offset}, by have := row.isLt; omega⟩\n'
    text+=f'  have position : (⟨{offset} + index.val, by have := index.isLt; omega⟩ : Fin {total}) = row := by\n    apply Fin.ext\n    dsimp [index]\n    omega\n'
    text+=f'  have values := (congrArg (normalizeDecoderFields {setup}) (congrArg Rows.nativeRow position)).symm.trans (Rows.normalized_tail_row index)\n'
    text+=f'  let packedIndex : Fin ({setup}.realRows.length + {setup}.padding.length) := ⟨index.val, by exact index.isLt⟩\n'
    text+=f'  have result : normalizeDecoderFields {setup} (Rows.nativeRow row) = ({setup}.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) := values\n'
    text+=f'  have casts : ({setup}.row packedIndex).map (fun n : Nat => (n : Source.BaseField)) =\n      ({setup}.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField)) := by\n    apply Vector.ext\n    intro column bound\n    simp only [Vector.getElem_map]\n    exact (Setup.signedValue_cast _).symm\n'
    text+=f'  change normalizeDecoderFields {setup} (Rows.nativeRow row) = ({setup}.row packedIndex).map (fun n => (Setup.signedValue n : Source.BaseField))\n  exact result.trans casts\n\n'
    text+=f'theorem full_lookup (packed : Vector Source.BaseField {width}) (query : Vector Source.BaseField 9)\n    (normalized : normalizeDecoderFields {setup} packed = activeQuery query)\n    (member : (nativeSetup.imported.data.table "Airbender.Native.{MODELS.get(family,case)}").Contains #[] packed) : {setup}.lookup query :=\n'
    text+=f'  decoder_full_lookup_of_rows {setup} nativeSetup.imported.data (by decide +kernel)\n    leading_rows tail_rows packed query normalized _ member\n\n'
    text+=f'theorem lookup_sound (capacity : FieldCapacity.NoWrap babyBearModulus 65536)\n    (packed : Vector Source.BaseField {width}) (query : Vector Source.BaseField 9) (typed : query[0].val < 65536)\n    (normalized : normalizeDecoderFields {setup} packed = activeQuery query)\n    (member : (nativeSetup.imported.data.table "Airbender.Native.{MODELS.get(family,case)}").Contains #[] packed) :\n    (Trace.decoderTable pooledProgram .{kind}).Contains #[] query :=\n  Trace.NativeDecoder.Proofs.{data_module}.lookup_sound capacity query typed (full_lookup packed query normalized member)\n\nend {owner}\n'
    return target,text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--family',choices=SPECS,action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for family in args.family or SPECS:
        name,text=module(family);path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('decoder membership scaffold changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
        print(name,flush=True)
        if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
