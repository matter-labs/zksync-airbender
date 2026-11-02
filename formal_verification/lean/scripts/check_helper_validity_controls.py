#!/usr/bin/env python3
"""Reject incomplete helper captures and changes to exact transport equality."""
import argparse
from check_clean_argument_controls import compile_source
from gkr_packed_helper_validity import CASES, dimensions, native, original


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=CASES,action='append')
    args=parser.parse_args()
    prefix='''import Airbender.Proofs.GKRProtocol.NumericHelperValidityChecks
import Airbender.Import.GKRProtocol.NumericHelperValidityImport
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
open Airbender Airbender.Compiler NumericHelperValidityChecks
namespace HelperValidityControl
set_option maxRecDepth 8192
def tiny : Capture := ⟨[2],1,[([(1,[0]),(0,[])],[(1,[0]),(0,[])])],
  [⟨[[(1,[0])]], [0]⟩], [⟨[(4,4)],[(1,[0]),(0,[])],[(1,[0]),(0,[])]⟩]⟩
'''
    exact='check babyBearModulus tiny = true'
    changes=[] if args.case else [
        ('protected coefficient',exact,'check babyBearModulus {tiny with protectedFields := [([(2,[0])],[(1,[0])])]} = true',''),
        ('borrow memory wire',exact,'check babyBearModulus {tiny with borrows := [⟨[[(1,[2])]], [0]⟩]} = true',''),
        ('strict borrow bound',exact,'check babyBearModulus {tiny with borrows := [⟨[[(1,[0])]], [1]⟩]} = true',''),
        ('transport address',exact,'check babyBearModulus {tiny with transports := [⟨[(4,5)],[(1,[0]),(0,[])],[(1,[0]),(0,[])]⟩]} = true',''),
        ('exact term order',exact,'check babyBearModulus {tiny with transports := [⟨[(4,4)],[(1,[0]),(0,[])],[(0,[]),(1,[0])]⟩]} = true',''),
        ('retained zero term',exact,'check babyBearModulus {tiny with transports := [⟨[(4,4)],[(1,[0]),(0,[])],[(1,[0])]⟩]} = true',''),
    ]
    for case in args.case or CASES:
        owner='Airbender.Compiler.HelperValidityChecks.'+case
        imports='import Airbender.Proofs.GKRProtocol.HelperValidityChecks.'+case+'.Data\n'
        protected,fields=dimensions(case)
        for field,size in [('protectedFields',protected),('borrows',fields),('transports',fields)]:
            for first in [0,(size-1)//4*4]:
                width=min(4,size-first);left=f'(({owner}.data.{field}.drop {first}).take {width})';right=f'(({owner}.original.{field}.drop {first}).take {width})'
                chunk=owner+'.'+field+str(first)+'.'+field
                changes.append((case+' '+field+' view '+str(first),left+' = '+chunk,'('+left+f').drop {width} = '+chunk,imports))
                changes.append((case+' '+field+' source '+str(first),chunk+' = '+right,'('+chunk+f').drop {width} = '+right,imports))
        changes += [(case+' borrow bound',owner+'.data.borrowBound = '+owner+'.original.borrowBound',owner+'.data.borrowBound + 1 = '+owner+'.original.borrowBound',imports),
                    (case+' coordinates',owner+'.data.coordinates = '+owner+'.original.coordinates',owner+'.data.coordinates ++ [0] = '+owner+'.original.coordinates',imports)]
    for label,expected,changed,imports in changes:
        for mutated,statement in [(False,expected),(True,changed)]:
            result=compile_source(imports+prefix+'numeric_data_binding result : '+statement+'\nend HelperValidityControl\n')
            if not mutated and result.returncode:raise SystemExit('Exact '+label+':\n'+result.stdout[-1800:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit('Changed '+label+':\n'+result.stdout[-1800:])
        print('PASS helper validity control:',label,flush=True)
    if not args.case:
        result=compile_source(prefix+'opaque hidden : Capture := tiny\nnumeric_helper_validity_capture data := hidden\nend HelperValidityControl\n')
        if not result.returncode or 'did not reduce to closed numeric data' not in result.stdout:raise SystemExit('Opaque helper payload:\n'+result.stdout[-1800:])
        print('PASS helper importer rejects opaque numeric payload',flush=True)
        # The legacy path still reconstructs every original check.
        text=original('AddSubCached').replace('Airbender.Compiler.HelperValidityNative.AddSubCached','HelperValidityLegacyControl')
        result=compile_source(text)
        if result.returncode:raise SystemExit('Legacy helper importer:\n'+result.stdout[-1800:])
        print('PASS legacy helper importer',flush=True)
        text=native('AddSubCached')[1];a=text.index('namespace Airbender.Compiler.HelperValidityNative.AddSubCached');b=text.index('import_helper_validity native',a);c=text.index('\n\ntheorem helper_graph_extends',b)
        imports=text[:a];header=text[a:b].replace('Airbender.Compiler.HelperValidityNative.AddSubCached','HelperValidityBadPhase')
        command=text[b:c];command=command.replace('phase 1 using_checks Airbender.Compiler.HelperValidityChecks.AddSubCached','phase 0 using_checks MissingFacts')
        result=compile_source(imports+header+command+'\nend HelperValidityBadPhase\n')
        if not result.returncode or 'data phase cannot accept checks' not in result.stdout:raise SystemExit('Unchecked data phase:\n'+result.stdout[-1800:])
        print('PASS data-only phase rejects semantic check injection',flush=True)
        header=header.replace('HelperValidityBadPhase','HelperValidityBadFacts')
        command=text[b:c];data=command.replace('phase 1 using_checks Airbender.Compiler.HelperValidityChecks.AddSubCached','phase 0')
        wrong=command.replace('Airbender.Compiler.HelperValidityChecks.AddSubCached','InvalidHelperFacts')
        source=imports+'namespace InvalidHelperFacts\ntheorem facts : True := True.intro\nend InvalidHelperFacts\n'+header+data+'\n\n'+wrong+'\nend HelperValidityBadFacts\n'
        result=compile_source(source)
        if not result.returncode or not any(mark in result.stdout.lower() for mark in ['invalid field','invalid projection','type mismatch']):raise SystemExit('Wrong helper facts:\n'+result.stdout[-1800:])
        print('PASS semantic finalizer rejects facts of the wrong type',flush=True)
    print('PASS',len(changes),'exact/kernel mutation pairs',flush=True)


if __name__=='__main__':main()
