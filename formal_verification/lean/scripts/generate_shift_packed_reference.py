#!/usr/bin/env python3
"""Encode the 128 basis rows of the unchanged shift reference."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def row(lane,p,byte,control):
 amount=control//8%32;op=control%8;mask=(1<<32)-1;v=(byte<<(8*p))&mask
 if op==1:v=(v<<amount)&mask
 elif op==2:v>>=amount
 elif op==3:v=(v>>amount) if v<(1<<31) else mask-((mask-v)>>amount)
 elif op==5:v=(byte<<(8*(3-p)))&mask if amount==0 else 0
 else:v=0
 return v//(256**lane)%256
def generated():
 branches=[]
 for position in range(4):
  for lane in range(4):
   for bit in range(8):
    cells=bytes(x for control in range(256) for x in (row(lane,position,1<<bit,control),0))
    branches.append(f'  | {position}, {lane}, {bit} => '+hex(int.from_bytes(cells,'little')))
 return """import Airbender.Proofs.Tables.ShiftPackedReference

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false

def basisRow : Nat → Nat → Nat → Nat
"""+'\n'.join(branches)+"""
  | _, _, _ => 0

end Airbender.Verification.ShiftPackedReference
"""

def row_tree(values):
 if len(values)==1:
  return '(.leaf '+hex(values[0])+')'
 return '(.branch '+row_tree(values[::2])+' '+row_tree(values[1::2])+')'

def numeric_rows():
 source="""import Airbender.Proofs.Tables.ShiftPackedExpectedRows

namespace Airbender.Verification.ShiftPackedReference
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

inductive RowTree where
  | leaf (value : Nat)
  | branch (left right : RowTree)

def RowTree.get (row : Nat) : RowTree → Nat
  | .leaf value => value
  | .branch left right => if row % 2 = 0 then left.get (row / 2) else right.get (row / 2)

"""
 for lane in range(4):
  values=[]
  for position in range(4):
   for byte in range(256):
    cells=bytes(x for control in range(256) for x in (row(lane,position,byte,control),0))
    values.append(int.from_bytes(cells,'little'))
  source+=f'def rowTree{lane} : RowTree := '+row_tree(values)+'\n\n'
 source+="""def rawRow (lane row : Nat) : Nat :=
  (match lane with
   | 0 => rowTree0
   | 1 => rowTree1
   | 2 => rowTree2
   | 3 => rowTree3
   | _ => .leaf 0).get row

def numericRow (lane row : Nat) : Nat :=
  if row < 1024 then rawRow lane row % 65536 ^ 256 else 0

end Airbender.Verification.ShiftPackedReference
"""
 return source


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--write',action='store_true')
 parser.add_argument('--check',action='store_true')
 args=parser.parse_args()
 for relative, content in [('ShiftPackedBasisData', generated()), ('ShiftPackedRowData', numeric_rows())]:
  path=ROOT/f'Airbender/Proofs/Tables/{relative}.lean'
  if not path.exists() or path.read_text()!=content:
   if not args.write:
    raise ValueError('packed shift reference changed: '+relative)
   path.write_text(content)
 print('PASS 128 shift basis rows and 4096 packed byte rows')

if __name__=='__main__':
 main()
