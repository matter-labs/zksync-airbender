#!/usr/bin/env python3
"""Assemble checked physical decoder columns through the actual packing masks."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_decoder_tail_instances import SPECS


def module(family):
    case,data_module,setup,_=SPECS[family]
    data=json.loads((LEAN/f'artifacts/setup/{family}.json').read_text())
    width=len(data['columns']);offset=data['circuit']['offset_for_decoder_table'];total=data['trace_len'];tail=total-offset
    owner=f'Airbender.Compiler.DecoderTail.{case}.Rows';name=f'Airbender.Proofs.GKRProtocol.DecoderTail.{case}.Rows'
    text=''.join(f'import Airbender.Proofs.GKRProtocol.DecoderTail.{case}.Column{i}\n' for i in range(width))
    text+='import Airbender.Proofs.GKRProtocol.PackedDecoderNormalization\n'+f'import Airbender.Proofs.GKRProtocol.MaterializedNative.{case}Uncached\n\nnamespace {owner}\nopen Airbender Airbender.Compiler Airbender.Trace.NativeDecoder\n'
    text+='set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    text+=f'abbrev nativeSetup := Airbender.Compiler.MaterializedNative.{case}Uncached.native.model\n\n'
    text+=f'def nativeRow (row : Fin {total}) : Vector Source.BaseField {width} := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))\n\n'
    text+=f'theorem real_column_length (column : Fin {width}) :\n    ({setup}.realRows.columns[column.val].blocks.toList.map Setup.Block.length).sum = {setup}.realRows.length := by\n  fin_cases column <;> decide +kernel\n\n'
    text+=f'theorem tail_column (column : Fin {width}) (index : Nat) :\n    nativeSetup.imported.data.columns[column.val].get? ({offset} + index) =\n      if index < {setup}.realRows.length then {setup}.realRows.columns[column.val].get? index\n      else {setup}.padding.columns[column.val].get? (index - {setup}.realRows.length) := by\n'
    text+=f'  have values : nativeSetup.imported.data.columns[column.val].get? ({offset} + index) =\n      Setup.getFromBlocks ({setup}.realRows.columns[column.val].blocks.toList ++ {setup}.padding.columns[column.val].blocks.toList) index := by\n    fin_cases column\n'
    text+=''.join(f'    · exact Airbender.Compiler.DecoderTail.{case}.Column{i}.decoder_tail_value index\n' for i in range(width))
    text+='  rw [values, getFromBlocks_append, real_column_length column]\n  rfl\n\n'
    text+=f'def dataTail (index : Nat) : Vector Nat {width} :=\n  if index < {setup}.realRows.length then {setup}.realRows.columns.map (fun column => (column.get? index).getD 0)\n  else {setup}.padding.columns.map (fun column => (column.get? (index - {setup}.realRows.length)).getD 0)\n\n'
    text+=f'theorem packed_row (index : Fin ({setup}.realRows.length + {setup}.padding.length)) :\n    {setup}.row index = {setup}.normalize (dataTail index.val) := by\n  by_cases leading : index.val < {setup}.realRows.length\n'
    for condition in ['pos','neg']:
        text+=f'  · simp only [PackedSetup.row, if_{condition} leading, dataTail,\n      show {setup}.{"realRows" if condition=="pos" else "padding"}.offset = 0 from rfl, Nat.zero_add]\n    rfl\n'
    text+=f'\ntheorem raw_tail_row (index : Fin {tail}) :\n    nativeRow ⟨{offset} + index.val, by have := index.isLt; omega⟩ =\n      (dataTail index.val).map (fun n : Nat => (n : Source.BaseField)) := by\n  apply Vector.ext\n  intro column bound\n  simp only [nativeRow, Setup.TableData.row, Vector.getElem_map,\n    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]\n  by_cases leading : index.val < {setup}.realRows.length\n'
    for condition in ['pos','neg']:text+=f'  · simp only [dataTail, if_{condition} leading, Vector.getElem_map]\n    rfl\n'
    if offset==0:text=text.replace('  rw [Setup.signedValue_cast, tail_column ⟨column, bound⟩ index.val]\n','  rw [Setup.signedValue_cast]\n  have actual := tail_column ⟨column, bound⟩ index.val\n  simp only [Nat.zero_add] at actual\n  rw [actual]\n')
    text+=f'\ntheorem normalized_tail_row (index : Fin {tail}) :\n    normalizeDecoderFields {setup} (nativeRow ⟨{offset} + index.val, by have := index.isLt; omega⟩) =\n      ({setup}.row ⟨index.val, by exact index.isLt⟩).map (fun n : Nat => (n : Source.BaseField)) := by\n'
    text+=f'  exact (congrArg (normalizeDecoderFields {setup}) (raw_tail_row index)).trans\n    ((normalize_decoder_fields_cast {setup} (dataTail index.val)).trans\n      (congrArg (fun values : Vector Nat 10 => values.map (fun n : Nat => (n : Source.BaseField))) (packed_row ⟨index.val, by exact index.isLt⟩)).symm)\n\nend {owner}\n'
    return name,text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--family',choices=SPECS,action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for family in args.family or SPECS:
        name,text=module(family);path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('decoder row scaffold changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
        print(name,flush=True)
        if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
