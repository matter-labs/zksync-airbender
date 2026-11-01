#!/usr/bin/env python3
"""Check exact native base ports, residuals and complete source data."""
import argparse,subprocess,tempfile
from pathlib import Path
from gkr_packed_functional_base import CASES, base_bindings
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--case',choices=CASES,action='append');args=parser.parse_args()
prefix="""import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender.Compiler NumericFunctionalBaseChecks
namespace FunctionalBaseControl
set_option maxRecDepth 8192
def tiny : Data := ⟨[(20,20,1)],[(1,[0]),(0,[])],[(1,[0]),(0,[])]⟩
"""
changes=[('address return','check 7 [tiny] = true','check 7 [{tiny with ports := [(21,20,1)]}] = true',''),
 ('base flag','check 7 [tiny] = true','check 7 [{tiny with ports := [(20,20,0)]}] = true',''),
 ('invalid base flag','check 7 [tiny] = true','check 7 [{tiny with ports := [(20,20,2)]}] = true',''),
 ('residual coefficient','check 7 [tiny] = true','check 7 [{tiny with right := [(2,[0]),(0,[])]}] = true',''),
 ('residual coordinate','check 7 [tiny] = true','check 7 [{tiny with right := [(1,[1]),(0,[])]}] = true',''),
 ('zero term binding','tiny.left = [(1,[0]),(0,[])]','tiny.left = [(1,[0])]','')]
if args.case:changes=[]
for case in args.case or CASES:
 count=len(base_bindings(case))
 owner='Airbender.Compiler.FunctionalBaseChecks.'+case
 for first in [0,count-1]:
  width=1;left=f'({owner}.data.drop {first}).take {width}';right=f'(({owner}.originalEntries.drop {first}).take {width}).map encode'
  changes.append((case+' '+str(first),left+' = '+right,'('+left+').drop 1 = '+right,'import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.'+case+'.Data\n'))
for label,exact,changed,imports in changes:
 for mutated,statement in [(False,exact),(True,changed)]:
  with tempfile.TemporaryDirectory(prefix='functional-base-control-') as directory:
   p=Path(directory)/'Check.lean';p.write_text(imports+prefix+'numeric_data_binding result : '+statement+'\nend FunctionalBaseControl\n')
   r=subprocess.run(['lean','--tstack=32768','-j1',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  if not mutated and r.returncode:raise SystemExit('Exact '+label+':\n'+r.stdout[-2000:])
  if mutated and (not r.returncode or '(kernel) declaration type mismatch' not in r.stdout.lower()):raise SystemExit('Changed '+label+':\n'+r.stdout[-2000:])
 print('PASS base control:',label,flush=True)
print('PASS',len(changes),'exact controls; kernel rejects all mutations',flush=True)
if not args.case:
 source='''import Airbender.Import.GKRProtocol.NumericFunctionalBaseImport
open Airbender.Compiler
opaque hidden : List NumericFunctionalBaseChecks.Data := []
numeric_functional_base_capture rejected := hidden
'''
 with tempfile.TemporaryDirectory(prefix='functional-base-opaque-') as directory:
  path=Path(directory)/'Check.lean';path.write_text(source)
  result=subprocess.run(['lean','--tstack=32768','-j1',str(path)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
  raise SystemExit('Opaque base payload was not rejected:\n'+result.stdout[-2000:])
 print('PASS opaque functional base payload rejection')
