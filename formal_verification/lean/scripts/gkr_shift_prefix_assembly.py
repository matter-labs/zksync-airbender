#!/usr/bin/env python3
"""Assemble checked block spans into complete Shift prefix/padding identities."""
import argparse
import json
import os
import subprocess
from gkr_shift_prefix_instances import LEAN, plans, REGIONS, PER_MODULE


def module(artifact, column):
    stop, chunks = plans(artifact, column)
    target = f'GKRProtocol.ShiftPrefixNative.Column{column}'
    text = ''.join(f'import GKRProtocol.ShiftPrefixParts.Column{column}.Part{i}\n'
                   for i in range((len(chunks) + PER_MODULE - 1) // PER_MODULE))
    text += 'import Airbender.Review.Helpers.Tables.Bytes\nimport GKRProtocol.BlockCoverageImport\n\n'
    text += (f'namespace Airbender.Compiler.ShiftPrefixNative.Column{column}\n'
             'open Airbender Airbender.Compiler\nset_option warningAsError true\n'
             'set_option Elab.async false\nset_option maxRecDepth 131072\n'
             'set_option maxHeartbeats 16000000\n\n')
    full = f'Data.GKRSetup.ShiftBinop.setupColumn{column}'
    text += f'column_blocks_part suffix from {full} start {stop} stop {len(artifact["columns"][column]["blocks"])}\n'
    for name, stem in [('originals','original'), ('targets','target')]:
        text += f'noncomputable def {name} : List (List Setup.Block) := [' + ', '.join(f'{stem}{i}' for i in range(len(chunks))) + ']\n\n'
    cols = [f'(Verification.{r}.columns[({column} : Nat)])' for r in REGIONS] + [f'Verification.byteShiftColumn{column}']
    joined = ' ++ '.join(f'{c}.blocks.toList' for c in cols)
    text += f'column_parts_cover sourceCoverage from {full} parts [' + ', '.join(f'original{i}' for i in range(len(chunks))) + ', suffix]\n\n'
    text += (f'theorem sourceShape : {full}.blocks.toList = originals.flatten ++ suffix := by\n'
             '  apply sourceCoverage.trans\n  simp only [originals, List.flatten_cons, List.flatten_nil, ' + ('List.append_assoc, ' if len(chunks)>1 else '') + 'List.append_nil]\n\n')
    for kind,col in enumerate(cols):
        names=[f'target{i}Region{kind}' for i,chunk in enumerate(chunks) if any(k==kind for k,_,_ in chunk[-1])]
        text += f'column_parts_cover regionShape{kind} from {col} parts [' + ', '.join(names) + ']\n\n'
    text += (f'theorem targetShape : {joined} = targets.flatten := by\n'
             '  rw [' + ', '.join(f'regionShape{k}' for k in range(7)) + ']\n  simp only [targets, ' + ', '.join(f'target{i}' for i in range(len(chunks))) +
             ', List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]\n\n')
    text += ('theorem chunksChecked : List.Forall₂ (fun first second => normalizeSetupBlocks first = normalizeSetupBlocks second) originals targets := by\n'
             '  exact ' + ''.join(f'List.Forall₂.cons chunkChecked{i} (' for i in range(len(chunks))) + 'List.Forall₂.nil' + ')' * len(chunks) + '\n\n')
    text += ('theorem prefixLength : (originals.flatten.map Setup.Block.length).sum = 524545 := by\n'
             '  simp only [originals, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, ' + ', '.join(f'chunkLength{i}' for i in range(len(chunks))) + ']\n  rfl\n\n')
    lengths = [1,256,65536,65536,65536,65536]
    for k,length in enumerate(lengths):
        region=artifact['tables'][k]
        checks=[]
        for i,chunk in enumerate(chunks):
            if not any(kind==k for kind,_,_ in chunk[-1]):continue
            lo,hi=chunk[2:4]
            span=min(hi,region['offset']+region['length'])-max(lo,region['offset'])
            check=f'region{k}Part{i}Length'
            text += f'theorem {check} : (target{i}Region{k}.map Setup.Block.length).sum = {span} := by decide +kernel\n\n'
            checks.append(check)
        text += (f'theorem regionLength{k} : ({cols[k]}.blocks.toList.map Setup.Block.length).sum = {length} := by\n'
                 f'  rw [regionShape{k}]\n'
                 '  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, ' + ', '.join(checks) + ']\n  rfl\n\n')
    text += (f'theorem prefix_value (index : Fin 524545) :\n    {full}.get? index.val = Setup.getFromBlocks ({joined}) index.val := by\n'
             f'  change Setup.getFromBlocks {full}.blocks.toList index.val = _\n'
             '  rw [sourceShape, getFromBlocks_before_suffix _ _ _ (by rw [prefixLength]; exact index.isLt), targetShape]\n'
             '  exact normalized_chunks_agree originals targets chunksChecked index.val\n\n')
    text += (f'theorem padding_value (index : Fin 16777216) (lower : 1573121 ≤ index.val) :\n    {full}.get? index.val = some 0 := by\n'
             f'  change Setup.getFromBlocks {full}.blocks.toList index.val = some 0\n'
             '  rw [sourceShape, getFromBlocks_append, prefixLength, if_neg (by omega)]\n'
             f'  change Setup.getFromBlocks [Setup.Block.affine 1048576 {46 if column == 9 else 2013265920} 0, .affine 15204095 0 0] (index.val - 524545) = some 0\n'
             '  simp only [Setup.getFromBlocks, Setup.Block.length]\n'
             '  rw [if_neg (by omega), if_pos (by omega)]\n'
             '  apply constant_block_get\n  omega\n\n')
    offsets=[0,1,257,65793,131329,196865,262401]
    values=[f'(Setup.getFromBlocks {c}.blocks.toList (index.val - {off})).getD 0' for c,off in zip(cols,offsets)]
    formula=values[-1]
    region_formula='Verification.shiftRegionRow 6 (index.val - 262401)'
    for k in reversed(range(6)):
        formula=f'if index.val < {offsets[k+1]} then {values[k]} else {formula}'
        region_formula=f'if index.val < {offsets[k+1]} then Verification.shiftRegionRow {k} (index.val - {offsets[k]}) else {region_formula}'
    text += (f'theorem clean_value (index : Fin 524545) :\n    ({full}.get? index.val).getD 0 = (Verification.shiftBinopRow index)[({column} : Nat)] := by\n'
             f'  have formula : (Verification.shiftBinopRow index)[({column} : Nat)] = ({formula}) := by\n'
             f'    change ({region_formula})[({column} : Nat)] = _\n'
             '    split_ifs <;> simp only [Verification.shiftRegionRow, Vector.getElem_map] <;> rfl\n'
             '  rw [prefix_value, formula]\n'
             '  simp only [List.append_assoc, getFromBlocks_append, ' + ', '.join(f'regionLength{i}' for i in range(6)) + ', Nat.sub_sub, Nat.reduceAdd, Nat.sub_zero]\n'
             '  split_ifs <;> omega\n\n')
    text += f'end Airbender.Compiler.ShiftPrefixNative.Column{column}\n'
    return target,text


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--column',type=int,choices=range(10),action='append')
    p.add_argument('--write',action='store_true');p.add_argument('--check',action='store_true');p.add_argument('--build',action='store_true')
    a=p.parse_args();artifact=json.loads((LEAN/'artifacts/setup/shift-binop.json').read_text())
    for column in a.column or range(10):
        target,text=module(artifact,column);path=LEAN/(target.replace('.','/')+'.lean')
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('Shift prefix assembly changed: '+target)
        if a.write:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(target,flush=True)
        if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
