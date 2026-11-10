#!/usr/bin/env python3
"""Reject wrong worker addresses, missing pairs and invalid history bounds."""
import argparse
from check_clean_argument_controls import compile_source
from gkr_packed_worker_ports import CASES, dimensions


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=CASES,action='append')
    args=parser.parse_args()
    prefix='''import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks
import Airbender.Import.GKRProtocol.NumericWorkerPortImport
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericWorkerPortChecks
namespace WorkerPortControl
set_option maxRecDepth 8192
'''
    cases=[] if args.case else [
        ('address return','check ⟨[(4,4)], []⟩ = true','check ⟨[(4,5)], []⟩ = true',''),
        ('address class','check (encode ⟨[(.BaseLayerWitness 4,.BaseLayerWitness 4)], []⟩) = true',
         'check (encode ⟨[(.Cached 0 4,.BaseLayerWitness 4)], []⟩) = true',''),
        ('history boundary','check ⟨[], [(3,4)]⟩ = true','check ⟨[], [(4,4)]⟩ = true',''),
        ('zero coordinate','encode ⟨[(.BaseLayerWitness 0,.BaseLayerWitness 0)], []⟩ = encode ⟨[(.BaseLayerWitness 0,.BaseLayerWitness 0)], []⟩',
         'encode ⟨[], []⟩ = encode ⟨[(.BaseLayerWitness 0,.BaseLayerWitness 0)], []⟩',''),
        ('complete bounds','(⟨[], [(0,1),(0,1)]⟩ : Data) = ⟨[], [(0,1),(0,1)]⟩','(⟨[], [(0,1)]⟩ : Data) = ⟨[], [(0,1),(0,1)]⟩',''),
        ('complete pairs','(⟨[(0,0),(1,1)], []⟩ : Data) = ⟨[(0,0),(1,1)], []⟩','(⟨[(1,1)], []⟩ : Data) = ⟨[(0,0),(1,1)], []⟩',''),
    ]
    for case in args.case or CASES:
        owner='Airbender.Compiler.WorkerPortChecks.'+case
        imports='import Airbender.Proofs.GKRProtocol.WorkerPortChecks.'+case+'.Data\n'
        encode='(fun row => (AddressUniqueChecks.addressCode row.1, AddressUniqueChecks.addressCode row.2))'
        sizes=dimensions(case)
        for field,size in zip(['columns','bounds'],sizes,strict=True):
            for first in [0,(size-1)//4*4]:
                width=min(4,size-first)
                left=f'(({owner}.data.{field}.drop {first}).take {width})'
                right=f'(({owner}.original.{field}.drop {first}).take {width})'
                if field=='columns':right+='.map '+encode
                cases.append((case+' '+field+' '+str(first),left+' = '+right,'('+left+f').drop {width} = '+right,imports))
    for label,exact,changed,imports in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            result=compile_source(imports+prefix+'numeric_data_binding result : '+statement+'\nend WorkerPortControl\n')
            if not mutated and result.returncode:raise SystemExit('Exact '+label+':\n'+result.stdout[-1800:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed '+label+':\n'+result.stdout[-1800:])
        print('PASS worker port control:',label,flush=True)
    if not args.case:
        result=compile_source(prefix+'opaque hidden : Data := ⟨[], []⟩\nnumeric_worker_port_capture data := hidden\nend WorkerPortControl\n')
        if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:
            raise SystemExit('Opaque worker payload:\n'+result.stdout[-1800:])
        print('PASS strict worker importer rejects opaque payload',flush=True)
    print('PASS',len(cases),'exact/kernel mutation pairs',flush=True)


if __name__=='__main__':main()
