#!/usr/bin/env python3
"""Close retained Shift lookups through the exported prefix and padding proof."""
import argparse
import os
import re
import subprocess
from export_gkr_translations import LEAN
from gkr_clean_closed_instances import module as full_table_module


def module(mode):
    case='ShiftBinop'+mode.title()
    target,text=full_table_module('shift-binop-'+mode,case,'ShiftBinop',10)
    text=text.replace('import GKRProtocol.CleanGenericSetup','import GKRProtocol.ShiftSetupNative')
    text=text.replace(f'Airbender.Compiler.MaterializedNative.{case}.native.model.imported.data.table "Airbender.Native.ShiftBinop"','Verification.shiftBinopTable (p := babyBearModulus)')
    text=text.replace('(Airbender.ShiftBinop.clockConstraints (p := babyBearModulus) nativeSetup)','(Airbender.ShiftBinop.clockConstraints (p := babyBearModulus))')
    text=text.replace(f'Airbender.Compiler.CleanLinksNative.{case}.retained_clock_constraints nativeSetup ',f'Airbender.Compiler.CleanLinksNative.{case}.retained_clock_constraints ')
    begin=list(re.finditer(r'^theorem generic_lookup\d+\n',text,re.M))
    end=text.index('theorem retained_clock_from_source')
    for i in reversed(range(len(begin))):
        start=begin[i].start();stop=begin[i+1].start() if i+1<len(begin) else end
        block=text[start:stop]
        block=re.sub(r'  apply Airbender.Compiler.MaterializedNative\.[^\n]+\.generic_clean_contains[^\n]+\n',
                     '  apply ShiftSetupNative.clean_contains _ ?_ ?_ _\n',block)
        marker=block.index('  simp only [')
        setup=block[:marker];tail=block[marker:]
        tail='  · '+tail[2:].replace('\n  ','\n    ').rstrip()+'\n'
        tail+=('  · rw [Vector.getElem_map]\n'
               f'    change Airbender.Compiler.CleanGenericArgumentsNative.{case}.native.part0.genericExpression{i}_8.eval (Airbender.Compiler.CleanArithmeticNative.{case}.native.environment physical data) = 0\n'
               '    rw [same8]\n    rfl\n\n')
        text=text[:start]+setup+tail+text[stop:]
    return target,text


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mode',choices=['cached','uncached'],action='append')
    for option in ['write','check','build']:p.add_argument('--'+option,action='store_true')
    a=p.parse_args()
    for mode in a.mode or ['uncached','cached']:
        target,text=module(mode);path=LEAN/(target.replace('.','/')+'.lean')
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('Shift Clean proof changed: '+target)
        if a.write:path.write_text(text)
        print(target,flush=True)
        if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
