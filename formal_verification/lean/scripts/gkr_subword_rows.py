#!/usr/bin/env python3
"""Assemble checked subword prefix columns into the retained complete row view."""
import argparse
import json
from export_gkr_translations import LEAN
from gkr_subword_prefix import REGIONS


def content():
    artifact=json.loads((LEAN/'artifacts/setup/subword-memory.json').read_text())
    out=''.join(f'import Airbender.Proofs.GKRProtocol.SubwordPrefixNative.Column{i}\n' for i in range(9))
    out+='import Airbender.Proofs.GKRProtocol.MaterializedNative.SubwordMemoryUncached\n\nnamespace Airbender.Compiler.ROMNative.SubwordRows\nopen Airbender Airbender.Compiler Airbender.Setup\n'
    out+='set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    out+='abbrev nativeSetup := Airbender.Compiler.MaterializedNative.SubwordMemoryUncached.native.model\n\n'
    out+='def nativeRow (row : Fin 16777216) : Vector Source.BaseField 9 := (nativeSetup.imported.data.row row).map (fun n : Int => (n : Source.BaseField))\n\n'
    for i,name in enumerate(REGIONS):
        region=artifact['tables'][i];size=region['length'];offset=region['offset'];data=f'Verification.{name}'
        out+=f'theorem region{i}_column (column : Fin 9) (index : Fin {size}) :\n    nativeSetup.imported.data.columns[column.val].get? ({offset} + index.val) = {data}.columns[column.val].get? index.val := by\n  fin_cases column\n'
        out+=''.join(f'  · exact SubwordPrefixNative.Column{j}.region_value{i} index\n' for j in range(9))+'\n'
        out+=f'theorem region{i}_row (index : Fin {size}) :\n    nativeRow ⟨{offset} + index.val, by have := index.isLt; omega⟩ =\n      ({data}.columns.map (fun column => (column.get? index.val).getD 0)).map (fun n : Nat => (n : Source.BaseField)) := by\n'
        out+='  apply Vector.ext\n  intro column bound\n  simp only [nativeRow, TableData.row, Vector.getElem_map,\n    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n'
        out+='  rw [Setup.signedValue_cast]\n'
        if i==0:out+='  have same := region0_column ⟨column, bound⟩ index\n  simp only [Nat.zero_add] at same\n  rw [same]\n\n'
        else:out+=f'  rw [region{i}_column ⟨column, bound⟩ index]\n\n'
    out+='theorem prefix_row (index : Fin 13238273) :\n    nativeRow ⟨index.val, by have := index.isLt; omega⟩ =\n      (Verification.importedSubwordRow index).map (fun n : Nat => (n : Source.BaseField)) := by\n'
    def body(i,indent):
        region=artifact['tables'][i];size=region['length'];offset=region['offset'];name=REGIONS[i]
        lines=[f'have actual := region{i}_row ⟨index.val - {offset}, by have := index.isLt; omega⟩',
          f'have position : {offset} + (index.val - {offset}) = index.val := by omega',
          'simp only [position] at actual',
          f'have view : Verification.importedSubwordRow index = Verification.{name}.columns.map (fun column => (column.get? (index.val - {offset})).getD 0) := by']
        if i==0:
            lines+=['  have zero : index = ⟨0, by decide⟩ := by', '    apply Fin.ext', '    change index.val = 0', '    omega', '  rw [zero]', '  rfl']
        elif i<5:
            lines+=['  unfold Verification.importedSubwordRow', '  rw [if_pos (by change index.val < 655361; omega)]', '  unfold Verification.subwordNativeRow', '  rw [if_neg (by change index.val ≠ 0; omega)]']
            for j in range(1,i):
                upper=artifact['tables'][j]['offset']+artifact['tables'][j]['length']
                lines+=[f'  rw [if_neg (by change ¬index.val < {upper}; omega)]']
            upper=region['offset']+region['length']
            lines+=[f'  rw [if_pos (by change index.val < {upper}; omega)]', '  rfl']
        else:
            lines+=['  unfold Verification.importedSubwordRow', '  rw [if_neg (by change ¬index.val < 655361; omega)]']
            lines+=['  rw [if_pos (by change index.val < 4849665; omega)]' if i==5 else '  rw [if_neg (by change ¬index.val < 4849665; omega)]', '  rfl']
        lines+=['rw [view]', 'exact actual']
        return ''.join(indent+line+'\n' for line in lines)
    def cases(i,indent):
        if i==6:return body(i,indent)
        stop=artifact['tables'][i]['offset']+artifact['tables'][i]['length']
        return (indent+f'by_cases selected{i} : index.val < {stop}\n'+indent+'·\n'+body(i,indent+'  ')+indent+'·\n'+cases(i+1,indent+'  '))
    out+=cases(0,'  ')
    out+='\nend Airbender.Compiler.ROMNative.SubwordRows\n';return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();path=LEAN/'Airbender/Proofs/GKRProtocol/ROMNative/SubwordRows.lean';text=content()
    if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('subword row scaffold changed')
    if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
    print('Airbender.Proofs.GKRProtocol.ROMNative.SubwordRows')


if __name__=='__main__':main()
