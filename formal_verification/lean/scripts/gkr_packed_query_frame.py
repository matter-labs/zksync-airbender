#!/usr/bin/env python3
"""Check complete query-frame captures after exact numeric source binding."""
import argparse
from export_gkr_translations import LEAN
from gkr_packed_rotate_boundary import preflight

CASES=('AddSubCached','AddSubUncached')


def source(case):
    prefix='Airbender.Compiler.'
    original=prefix+'QueryFrameNative.'+case+'.native'
    base=prefix+'FullArithmeticNative.'+case+'.native'
    lookup=prefix+'LookupNative.'+case+'.native'
    queries=prefix+'LookupSourceNative.'+case+'.native'
    return (f'NumericQueryFrameChecks.ofTyped {original}.fields {original}.coordinates\n'
            f'  {base}.originalProjection {lookup}.sourcePlacement {base}.inputBank {queries}.bank')


def modules(case):
    stem='Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+case
    owner='Airbender.Compiler.QueryFrameChecks.'+case
    header=f'namespace {owner}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\n\n'
    yield stem+'.Data',(f'import Airbender.Proofs.GKRProtocol.QueryFrameNative.{case}Inputs\n'
        'import Airbender.Import.GKRProtocol.NumericQueryFrameImport\n\n'+header+
        'numeric_query_frame_capture data := '+source(case)+'\n\nend '+owner+'\n')
    yield stem+'.Bindings',(f'import {stem}.Data\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header+
        'numeric_data_binding source_binding : data = '+source(case)+'\n\nend '+owner+'\n')
    original='Airbender.Compiler.QueryFrameNative.'+case+'.native'
    base='Airbender.Compiler.FullArithmeticNative.'+case+'.native'
    lookup='Airbender.Compiler.LookupNative.'+case+'.native'
    queries='Airbender.Compiler.LookupSourceNative.'+case+'.native'
    yield stem+'.Certificate',(f'import {stem}.Bindings\n\n'+header+
        'theorem checked : NumericQueryFrameChecks.check data = true := by decide +kernel\n\n'+
        f'theorem originalChecked : {original}.fields.all (fun field =>\n'
        f'    erasureUntouched {original}.coordinates (field.polynomial {base}.originalProjection) &&\n'
        f'      field.transportCheck {base}.originalProjection {lookup}.sourcePlacement\n'
        f'        {base}.inputBank {queries}.bank) = true :=\n'
        f'  NumericQueryFrameChecks.check_sound_of_binding data {original}.fields {original}.coordinates\n'
        f'    {base}.originalProjection {lookup}.sourcePlacement {base}.inputBank {queries}.bank\n'
        '    source_binding checked\n\nend '+owner+'\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--case',choices=CASES,action='append')
    parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true');args=parser.parse_args()
    for case in args.case or CASES:
        generated=list(modules(case))
        if args.write:preflight(generated)
        for module,text in generated:
            path=LEAN/(module.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('numeric query frame changed: '+module)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(module)


if __name__=='__main__':main()
