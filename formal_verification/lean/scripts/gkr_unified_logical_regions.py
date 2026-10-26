#!/usr/bin/env python3
"""Connect physical native region enumeration to the retained unified table order."""
import argparse
import json
from export_gkr_translations import LEAN

TAGS=[0,3,52,53,54,8,9,1,5,2,51,47,48,49,50]


def content():
    artifact=json.loads((LEAN/'artifacts/setup/unified.json').read_text());by_tag={r['id']:r for r in artifact['tables']}
    starts=[0]
    for tag in TAGS:starts.append(starts[-1]+by_tag[tag]['length'])
    assert starts[-1]==1048961
    out='import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup\n\nnamespace Airbender.Compiler.UnifiedLogicalRegions\nopen Airbender\nopen Airbender.UnifiedReduced.Setup\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    for k,tag in enumerate(TAGS):
        start=starts[k];size=by_tag[tag]['length'];n=f'({start} + index.val)'
        out+=f'theorem region{k}_row (index : Fin {size}) :\n    importedRow ⟨{start} + index.val, by have := index.isLt; omega⟩ = nativeFixedRow ⟨{k}, by decide⟩ index.val := by\n'
        if k==0:
            out+='  have zero : index = ⟨0, by decide⟩ := by\n    apply Fin.ext\n    change index.val = 0\n    have := index.isLt\n    omega\n  rw [zero]\n  rfl\n\n';continue
        out+='  have bound := index.isLt\n  unfold importedRow\n'
        out+=f'  rw [dif_pos (by change {n} < 1048961; omega)]\n  unfold fixedRow\n'
        out+=f'  rw [dif_{"pos" if k<7 else "neg"} (by change '+('' if k<7 else '¬')+f'{n} < 524545; omega)]\n'
        if k<7:
            out+='  unfold binaryRow\n'
            for j in range(1,k+1):out+=f'  rw [if_neg (by change ¬{n} < {starts[j]}; omega)]\n'
            if k<6:out+=f'  rw [if_pos (by change {n} < {starts[k+1]}; omega)]\n'
            out+=f'  have shifted : {n} - logicalFixedOffset {k} = index.val := by\n    change {n} - {start} = index.val\n    omega\n  rw [shifted]\n  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)\n\n'
        else:
            for j in range(8,min(k+1,12)):out+=f'  rw [if_neg (by change ¬{n} < {starts[j]}; omega)]\n'
            if k<11:
                out+=f'  rw [if_pos (by change {n} < {starts[k+1]}; omega)]\n'
                out+=f'  have shifted : {n} - logicalFixedOffset {k} = index.val := by\n    change {n} - {start} = index.val\n    omega\n  rw [shifted]\n  exact congrArg (fun kind : Fin 15 => nativeFixedRow kind index.val) (Fin.ext rfl)\n\n'
            else:
                out+='  unfold rotateRow\n'
                out+=f'  have quotient : ({n} - logicalFixedOffset 11) / 65536 = {k-11} := by\n    change ({n} - 786817) / 65536 = {k-11}\n    omega\n'
                out+=f'  have remainder : ({n} - logicalFixedOffset 11) % 65536 = index.val := by\n    change ({n} - 786817) % 65536 = index.val\n    omega\n  apply congrArg₂ nativeFixedRow\n  · apply Fin.ext\n    change 11 + (({n} - logicalFixedOffset 11) / 65536) = {k}\n    rw [quotient]\n  · exact remainder\n\n'
    out+='end Airbender.Compiler.UnifiedLogicalRegions\n';return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();text=content();path=LEAN/'Airbender/Proofs/GKRProtocol/UnifiedLogicalRegions.lean'
    if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified logical region scaffold changed')
    if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
    print('Airbender.Proofs.GKRProtocol.UnifiedLogicalRegions')


if __name__=='__main__':main()
