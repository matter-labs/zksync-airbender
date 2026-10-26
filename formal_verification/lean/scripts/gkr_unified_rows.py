#!/usr/bin/env python3
"""Connect every actual unified non-decoder row to the retained reordered table."""
import argparse
import json
import re
from export_gkr_translations import LEAN
from gkr_unified_prefix import DATA,PREFIX
from gkr_unified_logical_regions import TAGS


def column_module(column):
    artifact=json.loads((LEAN/'artifacts/setup/unified.json').read_text())
    stem=f'UnifiedPrefixNative.Column{column}' if column==1 else f'UnifiedAllPrefix.Column{column}'
    owner=f'Airbender.Compiler.{stem}'
    name=f'Airbender.Proofs.GKRProtocol.UnifiedRegionColumns.Column{column}'
    out=f'import Airbender.Proofs.GKRProtocol.{stem}\nimport Airbender.Proofs.GKRProtocol.SixteenRegions\n\nnamespace Airbender.Compiler.UnifiedRegionColumns.Column{column}\nopen Airbender Airbender.Compiler {owner}\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    cols=[f'(UnifiedReduced.Setup.{DATA[r["id"]]}.columns[({column} : Nat)])' for r in artifact['tables']]
    for i,region in enumerate(artifact['tables']):
        size=region['length'];offset=region['offset'];data=cols[i]
        out+=f'noncomputable def front{i} : List Setup.Block := '+(' ++ '.join(c+'.blocks.toList' for c in cols[:i]) or '[]')+'\n'
        out+=f'noncomputable def back{i} : List Setup.Block := '+(' ++ '.join(c+'.blocks.toList' for c in cols[i+1:]) or '[]')+'\n\n'
        out+=f'theorem regionPrefix{i} : (front{i}.map Setup.Block.length).sum = {offset} := by\n'
        if i==0:out+='  rfl\n\n'
        elif i==1:out+='  exact regionLength0\n\n'
        else:out+='  simp only [front'+str(i)+', List.map_append, List.sum_append, '+', '.join(f'regionLength{j}' for j in range(i))+']\n\n'
        out+=f'theorem region_value{i} (index : Fin {size}) :\n    Data.GKRSetup.Unified.setupColumn{column}.get? ({offset} + index.val) = {data}.get? index.val := by\n'
        out+=f'  apply (prefix_value ⟨{offset} + index.val, by have := index.isLt; omega⟩).trans\n'
        out+=f'  have shape : regionBlocks = front{i} ++ ({data}.blocks.toList ++ back{i}) := by\n'
        out+=f'    exact sixteen_region_shape{i} '+ ' '.join(c+'.blocks.toList' for c in cols)+'\n'
        out+='  rw [shape]\n'
        out+=f'  have skipped := Setup.Proofs.skip_blocks front{i} ({data}.blocks.toList ++ back{i}) index.val\n  rw [regionPrefix{i}] at skipped\n'
        out+=f'  exact skipped.trans (getFromBlocks_before_suffix _ _ index.val (by rw [regionLength{i}]; exact index.isLt))\n\n'
    return name,out+'end Airbender.Compiler.UnifiedRegionColumns.Column'+str(column)+'\n'


def rows_module():
    artifact=json.loads((LEAN/'artifacts/setup/unified.json').read_text())
    by_tag={r['id']:r for r in artifact['tables']};starts={};pos=0
    for tag in TAGS:starts[tag]=pos;pos+=by_tag[tag]['length']
    starts[34]=pos
    name='Airbender.Proofs.GKRProtocol.ROMNative.UnifiedRows'
    out=''.join(f'import Airbender.Proofs.GKRProtocol.UnifiedRegionColumns.Column{i}\n' for i in range(10))
    out+='import Airbender.Proofs.GKRProtocol.MaterializedNative.UnifiedUncached\nimport Airbender.Proofs.GKRProtocol.UnifiedLogicalRegions\n\nnamespace Airbender.Compiler.ROMNative.UnifiedRows\nopen Airbender Airbender.Compiler Airbender.Setup\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    out+='abbrev nativeSetup := Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model\n\ndef nativeRow (row : Fin 8388608) : Vector Source.BaseField 10 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))\n\n'
    for i,region in enumerate(artifact['tables']):
        size=region['length'];offset=region['offset'];data=f'UnifiedReduced.Setup.{DATA[region["id"]]}'
        out+=f'theorem region{i}_column (column : Fin 10) (index : Fin {size}) :\n    nativeSetup.imported.data.columns[column.val].get? ({offset} + index.val) = {data}.columns[column.val].get? index.val := by\n  fin_cases column\n'
        out+=''.join(f'  · exact UnifiedRegionColumns.Column{j}.region_value{i} index\n' for j in range(10))+'\n'
        out+=f'theorem region{i}_row (index : Fin {size}) :\n    nativeRow ⟨{offset} + index.val, by have := index.isLt; omega⟩ =\n      ({data}.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by\n'
        out+='  apply Vector.ext\n  intro column bound\n  simp only [nativeRow, TableData.row, Vector.getElem_map,\n    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n  rw [Setup.signedValue_cast]\n'
        if i==0:out+='  have same := region0_column ⟨column, bound⟩ index\n  simp only [Nat.zero_add] at same\n  rw [same]\n\n'
        else:out+=f'  rw [region{i}_column ⟨column, bound⟩ index]\n\n'
        logical=starts[region['id']]
        out+=f'theorem region{i}_retained (index : Fin {size}) :\n    nativeRow ⟨{offset} + index.val, by have := index.isLt; omega⟩ =\n      (UnifiedReduced.Setup.importedRow ⟨{logical} + index.val, by have := index.isLt; omega⟩).map (fun n : Nat => (n : Source.BaseField)) := by\n'
        out+=f'  rw [region{i}_row]\n'
        if region['id']==34:
            out+='  simp only [UnifiedReduced.Setup.importedRow, dif_neg (by have := index.isLt; omega : ¬1048961 + index.val < 1048961), Nat.add_sub_cancel_left]\n\n'
        else:
            k=TAGS.index(region['id'])
            out+=f'  rw [UnifiedLogicalRegions.region{k}_row]\n  rfl\n\n'
    out+=f'theorem prefix_member (index : Fin {PREFIX}) :\n    (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] (nativeRow ⟨index.val, by have := index.isLt; omega⟩) := by\n'
    def body(i,indent):
        region=artifact['tables'][i];offset=region['offset'];logical=starts[region['id']]
        lines=[f'let localIndex : Fin {region["length"]} := ⟨index.val - {offset}, by have := index.isLt; omega⟩',f'have actual := region{i}_retained localIndex',f'have position : {offset} + localIndex.val = index.val := by dsimp [localIndex]; omega',f'have same : nativeRow ⟨{offset} + localIndex.val, by have := localIndex.isLt; omega⟩ = nativeRow ⟨index.val, by have := index.isLt; omega⟩ := congrArg nativeRow (Fin.ext position)',f'exact ⟨⟨{logical} + localIndex.val, by change {logical} + localIndex.val < 2097537; have := localIndex.isLt; omega⟩, same.symm.trans actual⟩']
        return ''.join(indent+line+'\n' for line in lines)
    def cases(i,indent):
        if i==15:return body(i,indent)
        r=artifact['tables'][i]
        return indent+f'by_cases selected{i} : index.val < {r["offset"]+r["length"]}\n'+indent+'·\n'+body(i,indent+'  ')+indent+'·\n'+cases(i+1,indent+'  ')
    out+=cases(0,'  ')
    return name,out+'\nend Airbender.Compiler.ROMNative.UnifiedRows\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column',type=int,choices=range(10),action='append');parser.add_argument('--rows',action='store_true')
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();modules=[]
    if args.rows:modules=[rows_module()]
    else:
        for column in args.column or range(10):
            name,text=column_module(column)
            beginning=text[:text.index('noncomputable def front0')]
            ending='end Airbender.Compiler.UnifiedRegionColumns.Column'+str(column)+'\n'
            chunks=re.split(r'(?=noncomputable def front[0-9]+ :)',text[len(beginning):-len(ending)])
            chunks=[chunk for chunk in chunks if chunk]
            for i in range(0,16,4):modules.append((f'Airbender.Proofs.GKRProtocol.UnifiedRegionParts.Column{column}.Part{i//4}',beginning+''.join(chunks[i:i+4])+ending))
            modules.append((name,''.join(f'import Airbender.Proofs.GKRProtocol.UnifiedRegionParts.Column{column}.Part{i}\n' for i in range(4))))
    for name,text in modules:
        path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified row scaffold changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(name)

if __name__=='__main__':main()
