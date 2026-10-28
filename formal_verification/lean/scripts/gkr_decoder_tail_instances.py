#!/usr/bin/env python3
"""Check complete real-decoder/padding tails at exact native block boundaries."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_rom_columns import length

SPECS={
 'add-sub':('AddSub','AddSub','addSubSetup',None),
 'jump-branch':('JumpBranch','JumpBranch','jumpBranchSetup',None),
 'mul-div':('MulDiv','MulDiv','mulDivSetup',None),
 'shift-binop':('ShiftBinop','ShiftBinop','shiftBinopSetup','ShiftPrefixNative'),
 'word-memory':('WordMemory','WordMemory','wordMemorySetup',None),
 'subword-memory':('SubwordMemory','Subword','subwordSetup','SubwordPrefixNative'),
}


def modules(family):
    case,data_module,setup,reuse=SPECS[family]
    data=json.loads((LEAN/f'artifacts/setup/{family}.json').read_text());offset=data['circuit']['offset_for_decoder_table']
    for column,description in enumerate(data['columns']):
        total=0;stop=0
        while total<offset:total+=length(description['blocks'][stop]);stop+=1
        if total!=offset:raise ValueError('decoder boundary crosses a block; needs checked extra span: '+family)
        name=f'Airbender.Proofs.GKRProtocol.DecoderTail.{case}.Column{column}';owner=f'Airbender.Compiler.DecoderTail.{case}.Column{column}'
        full=f'Data.GKRSetup.{case}.setupColumn{column}'
        text='import Airbender.Proofs.GKRProtocol.DecoderTailNormalization\n'
        text+=(f'import Airbender.Proofs.GKRProtocol.{reuse}.Column{column}\n' if reuse else f'import Airbender.Data.GKRSetup.{case}\nimport Airbender.Import.GKRProtocol.BlockCoverageImport\n')
        text+=f'import Airbender.Data.Decoder.Setup.{data_module}\n\nnamespace {owner}\nopen Airbender Airbender.Compiler'
        if reuse:text+=f' Airbender.Compiler.{reuse}.Column{column}'
        text+='\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
        if reuse:prefix='originals.flatten'
        else:
            prefix='prefixBlocks'
            text+=f'column_blocks_part prefixBlocks from {full} start 0 stop {stop}\n'
            text+=f'column_blocks_part suffix from {full} start {stop} stop {len(description["blocks"])}\n\n'
            if stop:
                text+=f'column_parts_cover coverage from {full} parts [prefixBlocks, suffix]\n\n'
                text+=f'theorem sourceShape : {full}.blocks.toList = prefixBlocks ++ suffix := by\n  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using coverage\n\n'
            else:text+=f'theorem sourceShape : {full}.blocks.toList = prefixBlocks ++ suffix := by rfl\n\n'
            text+=f'theorem prefixLength : (prefixBlocks.map Setup.Block.length).sum = {offset} := by decide +kernel\n\n'
        text+=f'theorem tail_value (index : Nat) : {full}.get? ({offset} + index) = Setup.getFromBlocks suffix index := by\n'
        text+=f'  change Setup.getFromBlocks {full}.blocks.toList ({offset} + index) = _\n  rw [sourceShape]\n  have skipped := Setup.Proofs.skip_blocks {prefix} suffix index\n  rw [prefixLength] at skipped\n  exact skipped\n\n'
        text+=f'noncomputable def targetTail : List Setup.Block :=\n  Trace.NativeDecoder.{setup}.realRows.columns[{column}].blocks.toList ++\n  Trace.NativeDecoder.{setup}.padding.columns[{column}].blocks.toList\n\n'
        text+='theorem tail_checked : normalizeSetupBlocks suffix = normalizeSetupBlocks targetTail := by rfl\n\n'
        text+=f'theorem decoder_tail_value (index : Nat) : {full}.get? ({offset} + index) = Setup.getFromBlocks targetTail index :=\n'
        text+='  (tail_value index).trans ((normalizeSetupBlocks_sound suffix index).symm.trans\n    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans\n      (normalizeSetupBlocks_sound targetTail index)))\n\nend '+owner+'\n'
        yield name,text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--family',choices=SPECS,action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for family in args.family or SPECS:
        for name,text in modules(family):
            path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('native decoder tail scaffold changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
