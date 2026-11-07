#!/usr/bin/env python3
"""Bind every native shift output block to a balanced packed column."""
import argparse, json
from pathlib import Path
root=Path(__file__).resolve().parents[1]
from generate_packed_xor9 import block_length,term,ranges,tree,binding_tree
from gkr_unified_prefix import slice_block,value

def native_blocks(artifact,lane):
 region=next(x for x in artifact['tables'] if x['id']==9)
 if (region['length'],region['width'],region['key_columns'])!=(262144,8,4):
  raise ValueError('shift dimensions changed')
 blocks=[];position=0
 for b in artifact['columns'][lane+4]['blocks']:
  n=block_length(b);lo=max(region['offset'],position);hi=min(region['offset']+region['length'],position+n)
  if lo<hi:blocks.extend(x for _,x in slice_block(b,lo-position,hi-lo))
  position+=n
 if sum(map(block_length,blocks))!=262144:raise ValueError('incomplete shift region')
 return blocks

def branch(leaves):
 if len(leaves)==1:return leaves[0]
 mid=len(leaves)//2
 return f'(.branch {branch(leaves[:mid])} {branch(leaves[mid:])})'

def payload(blocks):
 cells=bytearray()
 for b in blocks:
  for i in range(block_length(b)):
   v=value(b,i)
   if not 0<=v<256:raise ValueError('output exceeds a byte')
   cells.extend((v,0))
 return hex(int.from_bytes(cells, 'little'))

def generated(artifact,lane):
 blocks=native_blocks(artifact,lane);parts=ranges(0,len(blocks),8)
 ns=f'Airbender.Verification.ShiftPackedEncoding.Lane{lane}'
 base=f'Airbender/Proofs/Tables/ShiftPackedEncoding/Column{lane}'
 data=f'''import Airbender.Data.Tables.Shift.Column{lane+4}
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}Requests
import Airbender.Proofs.Tables.PackedWordColumn
import Airbender.Proofs.Tables.LiteralColumnParts
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace {ns}
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks PackedWordColumn
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

literal_column_parts sourceColumn from byteShiftColumn{lane+4} depth 8

'''
 for i,(lo,hi) in enumerate(parts):
  data+=f'def codes{i} : List Code := ['+', '.join(map(term,blocks[lo:hi]))+']\n'
 data+='\ndef blocks : List Code := '+tree([f'codes{i}' for i in range(256)])+'\n\n'
 for i in range(256):
  data+=f'numeric_data_binding binding{i} : codes{i}.map (Code.decode 65536) = sourceColumnBlocks{i}.toList\n'
 data+='\ntheorem source_binding : blocks.map (Code.decode 65536) = sourceColumn.blocks.toList := by\n'
 data+='  have joined : sourceColumn.blocks = '+tree([f'sourceColumnBlocks{i}' for i in range(256)])+' := rfl\n'
 data+='  rw [joined]\n  simpa only [blocks, List.map_append, Array.toList_append] using '+binding_tree(0,256)+'\n\n'
 for i,(lo,hi) in enumerate(parts):
  data+=f'def leaf{i} : Tree := .leaf codes{i} {sum(map(block_length,blocks[lo:hi]))} {payload(blocks[lo:hi])}\n'
 data+='\ndef column : Tree := '+branch([f'leaf{i}' for i in range(256)])+'\n\n'
 data+='theorem column_blocks : column.blocks = blocks := rfl\n'
 data+='theorem row_count : column.length = 262144 := by decide +kernel\n'
 data+='numeric_data_binding requests_binding : column.requests 0 = requests\n'
 data+=f'\nend {ns}\n'
 cert=f'''import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}Data
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}Reference

namespace {ns}
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks PackedWordColumn
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem checked : column.check = true := by decide +kernel

theorem native_get (index : Nat) (within : index < 262144) :
    getFromBlocks byteShiftColumn{lane+4}.blocks.toList index =
      some (PackedSignedRun.digit 65536 column.payload index) := by
  have result := (column.check_sound checked).2.2 index (by simpa only [row_count] using within)
  rw [column_blocks, source_binding] at result
  exact result

theorem reference_checked : column.checkLeaves (ShiftPackedReference.checkSpan {lane}) 0 = true := by
  rw [column.checkLeaves_requests, requests_binding]
  exact requests_checked

theorem native_checks : checkBlocks (ShiftCertificate.outputByte {lane}) 0
    byteShiftColumn{lane+4}.blocks.toList = true := by
  rw [ShiftCertificate.outputByte_normalized]
  have result := column.checkLeaves_sound (ShiftCertificate.outputNatByte {lane})
    (ShiftPackedReference.checkSpan {lane})
    (ShiftPackedReference.checkSpan_sound {lane} (by decide +kernel)) 0 checked reference_checked
  rw [column_blocks, source_binding] at result
  exact result

end {ns}
'''
 requests=f'''import Airbender.Proofs.Tables.PackedWordColumn

namespace {ns}
open Airbender.Setup.Proofs.PackedWordColumn
set_option warningAsError true
set_option Elab.async false

def requests : List Request := [
''' + ',\n'.join(f'  ⟨{sum(map(block_length, blocks[:lo]))}, {sum(map(block_length, blocks[lo:hi]))}, {payload(blocks[lo:hi])}⟩' for lo,hi in parts) + ']\n\nend '+ns+'\n'
 reference=f'''import Airbender.Proofs.Tables.ShiftPackedEncoding.Column{lane}Requests
import Airbender.Proofs.Tables.ShiftPackedRows

namespace {ns}
open Airbender.Setup.Proofs.PackedWordColumn
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem requests_checked : checkRequests (ShiftPackedReference.checkSpan {lane}) requests = true := by
  decide +kernel

end {ns}
'''
 return {base+'Data.lean':data,base+'.lean':cert,base+'Requests.lean':requests,base+'Reference.lean':reference}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--write', action='store_true')
 parser.add_argument('--check', action='store_true')
 args=parser.parse_args()
 artifact=json.loads((root/'artifacts/setup/shift-binop.json').read_text())
 for lane in range(4):
  for relative,content in generated(artifact,lane).items():
   path=root/relative
   if not path.exists() or path.read_text()!=content:
    if not args.write:
     raise ValueError('packed shift encoding changed: '+relative)
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(content)
 print('PASS all four complete native shift encodings')

if __name__=='__main__':
 main()
