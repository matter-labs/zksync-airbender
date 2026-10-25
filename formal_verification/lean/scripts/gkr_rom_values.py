#!/usr/bin/env python3
"""Check every unified ROM field against its independently imported region."""
import argparse
import json
from export_gkr_translations import LEAN
from gkr_rom_columns import length


def content():
    artifact=json.loads((LEAN/'artifacts/setup/unified.json').read_text())
    out=''.join(f'import GKRProtocol.ROMColumns.Unified.Column{i}\n' for i in range(10))
    out+='import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData\nimport Airbender.Proofs.Tables.ZeroTail\n\n'
    out+='namespace Airbender.Compiler.ROMNative.UnifiedValues\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    cutoff={1:4,2:4,3:1,4:0,5:3,6:3,7:3,8:0}
    for col in range(10):
        owner=f'Airbender.Compiler.ROMColumns.Unified.Column{col}'
        selected=owner+'.selectedColumn';target=f'UnifiedReduced.Setup.nativeROMData.columns[{col}]'
        pos=0
        for block in artifact['columns'][col]['blocks']:
            if pos+length(block)>590081:break
            pos+=length(block)
        shift=590081-pos
        if col in cutoff:
            cut=cutoff[col]
            out+=f'private theorem sourceTail{col} : Setup.Proofs.zeroTail {shift+cut} {selected}.blocks.toList = true := by decide +kernel\n\n'
            out+=f'private theorem targetTail{col} : Setup.Proofs.zeroTail {cut} {target}.blocks.toList = true := by decide +kernel\n\n'
            out+=f'private theorem targetExtent{col} : ({target}.blocks.toList.map Setup.Block.length).sum = 1048576 := by decide +kernel\n\n'
        out+=f'theorem column{col} (index : Fin 1048576) :\n    Data.GKRSetup.Unified.setupColumn{col}.get? (590081 + index.val) = {target}.get? index.val := by\n  rw [{owner}.column_value index]\n'
        if col in [0,9]:out+='  rw [Nat.zero_add]\n  rfl\n\n';continue
        cut=cutoff[col]
        if cut:
            out+=f'  by_cases leading : index.val < {cut}\n  · generalize eq : index.val = n at *\n    interval_cases n'+(' <;> rfl' if cut>1 else '; rfl')+'\n  · '
            indent='    '
        else:
            out+='  ';indent='  '
        out+=f'have sourceValue := Setup.Proofs.zeroTail_sound {shift+cut} {selected}.blocks.toList\n'
        out+=indent+f'  sourceTail{col} ({shift} + index.val) (by omega) (by rw [{owner}.selectedLength]; have := index.isLt; omega)\n'
        out+=indent+f'have targetValue := Setup.Proofs.zeroTail_sound {cut} {target}.blocks.toList\n'
        out+=indent+f'  targetTail{col} index.val (by omega) (by rw [targetExtent{col}]; exact index.isLt)\n'
        out+=indent+'exact sourceValue.trans targetValue.symm\n\n'
    out+='end Airbender.Compiler.ROMNative.UnifiedValues\n';return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();path=LEAN/'GKRProtocol/ROMNative/UnifiedValues.lean';text=content()
    if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified ROM values scaffold changed')
    if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
    print('GKRProtocol.ROMNative.UnifiedValues')


if __name__=='__main__':main()
