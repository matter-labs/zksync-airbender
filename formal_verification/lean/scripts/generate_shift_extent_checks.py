#!/usr/bin/env python3
"""Derive all Shift output extents from complete numeric length checks."""
import argparse
import json
import re
import subprocess
from pathlib import Path
from generate_shift_packed_encoding import native_blocks
from generate_packed_xor9 import block_length, ranges, tree

ROOT=Path(__file__).resolve().parents[1]


def generated(artifact,lane):
    blocks=native_blocks(artifact,lane)
    parts=ranges(0,len(blocks),4)
    leaves=ranges(0,len(blocks),8)
    owner=f'Airbender.Verification.ShiftExtentChecks.Lane{lane}'
    encoded=f'Airbender.Verification.ShiftPackedEncoding.Lane{lane}'
    stem=f'Airbender.Proofs.Tables.ShiftExtentChecks{lane}'
    header=(f'namespace {owner}\nopen Airbender.Setup Airbender.Setup.Proofs Airbender.Verification\n'
            'open PackedWordBlocks PackedWordColumn\nset_option warningAsError true\n'
            'set_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    data=(f'import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}Data\n'
          f'import Airbender.Proofs.Tables.ShiftOutputPartitions{lane}\n'
          'import Airbender.Proofs.Tables.PackedLengthChecks\n\n'+header)
    rows=[]
    for part,(first,last) in enumerate(parts):
        chosen=[index for index,(lo,hi) in enumerate(leaves) if first<=lo and hi<=last]
        if chosen!=list(range(16*part,16*(part+1))):
            raise ValueError('Shift native partition nesting changed')
        rows.append(sum(map(block_length,blocks[first:last])))
        codes=tree([f'{encoded}.codes{index}' for index in chosen])
        source=tree([f'{encoded}.sourceColumnBlocks{index}' for index in chosen])
        data+=f'def part{part} : List Code := {codes}\n\n'
        data+=(f'theorem binding{part} : part{part}.map (Code.decode 65536) = ShiftCertificate.output{lane}Blocks{part}.toList := by\n'
               f'  have joined : ShiftCertificate.output{lane}Blocks{part} = {source} := rfl\n'
               '  rw [joined]\n'
               f'  simp only [part{part}, List.map_append, Array.toList_append, '+', '.join(f'{encoded}.binding{index}' for index in chosen)+']\n\n')
    data+='def requests : List PackedLengthChecks.Request := ['+', '.join(f'⟨part{part}, {row}⟩' for part,row in enumerate(rows))+']\n\n'
    data+='theorem checked : PackedLengthChecks.check requests = true := by decide +kernel\n\nend '+owner+'\n'
    yield stem,data
    wrapper=(f'import {stem}\nimport Airbender.Proofs.Tables.LiteralSizes\n'
             'import Airbender.Proofs.Tables.ImportedBlocks\n\nnamespace Airbender.Verification.ShiftCertificate\n'
             'open Airbender.Setup Airbender.Verification\nset_option warningAsError true\n'
             'set_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    for part,row in enumerate(rows):
        wrapper+=(f'theorem output{lane}_extent{part} : (output{lane}Blocks{part}.toList.map Block.length).sum = {row} := by\n'
                  f'  rw [← {owner}.binding{part}]\n'
                  f'  exact PackedLengthChecks.check_sound_at {owner}.requests {owner}.checked ⟨{part}, by decide +kernel⟩\n\n')
    joined=tree([f'output{lane}Blocks{part}' for part in range(16)])
    wrapper+=(f'theorem output{lane}_coverage : (byteShiftColumn{lane+4}.blocks.toList.map Block.length).sum = 262144 := by\n'
              f'  have joined : byteShiftColumn{lane+4}.blocks = {joined} := rfl\n  rw [joined]\n'
              '  simp only [Array.toList_append, List.map_append, List.sum_append, '+', '.join(f'output{lane}_extent{part}' for part in range(16))+', Nat.reduceAdd]\n\n'
              'end Airbender.Verification.ShiftCertificate\n')
    yield f'Airbender.Proofs.Tables.ShiftOutputExtent{lane}',wrapper


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lane',type=int,choices=range(4),action='append')
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    artifact=json.loads((ROOT/'artifacts/setup/shift-binop.json').read_text())
    outputs=[]
    for lane in args.lane if args.lane is not None else range(4):
        capture=list(generated(artifact,lane))
        old=ROOT/(capture[-1][0].replace('.','/')+'.lean')
        contract=rf'theorem output{lane}_extent(\d+)\s*:[\s\S]*?\.sum\s*=\s*(\d+)'
        if old.exists() and re.findall(contract,old.read_text())!=re.findall(contract,capture[-1][1]):
            raise ValueError('original Shift extent statements changed')
        outputs.extend(capture)
    if args.write:
        for name,source in outputs:
            path=ROOT/(name.replace('.','/')+'.lean')
            if path.exists() and path.read_text()!=source and subprocess.run(
                    ['git','ls-files','--error-unmatch',str(path.relative_to(ROOT))],cwd=ROOT,
                    stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
                raise ValueError('refuse to replace untracked extent source: '+str(path))
    for name,source in outputs:
        path=ROOT/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):
            raise ValueError('Shift extent capture changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=source):
            path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(name)


if __name__=='__main__':main()
