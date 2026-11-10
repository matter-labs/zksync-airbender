#!/usr/bin/env python3
"""Reuse complete native checks for Shift and binary table coverage."""
import argparse
import json
import re
from gkr_shift_prefix_instances import LEAN, plans
from gkr_packed_rotate_boundary import preflight

STEM='Airbender.Proofs.Tables.ShiftMetadata'
OWNER='Airbender.Verification.ShiftMetadata'
TABLES=['byteXorData','byteOrData','byteAndData','byteTruncateData','byteShiftData']
SHIFT='''theorem shift_coverage (lane : Fin 10) :
    ((byteShiftData.columns[lane]).blocks.toList.map Block.length).sum = 262144'''
BINARY='''theorem binary_coverage (kind : Fin 4) (lane : Fin 10) :
    let data : TableData 10 := #v[byteXorData, byteOrData, byteAndData, byteTruncateData][kind]
    ((data.columns[lane]).blocks.toList.map Block.length).sum = 65536'''
NATIVE='''theorem native_cast (kind : Fin 7) (index : Fin (shiftData kind).length) :
    (shiftRegionRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((shiftData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus))'''
OUTPUT_COVERAGE='''theorem coverage (kind : Fin 3) :
    ((data (binaryKind kind)).columns[2].blocks.toList.map Block.length).sum = 65536'''


def cases(terms,family):
    result='(fun impossible => Fin.elim0 impossible)'
    for offset in reversed(range(len(terms))):
        motive=family.format(index='index'+'.succ'*offset)
        result=f'(Fin.cases (motive := fun index : Fin {len(terms)-offset} => {motive}) ({terms[offset]}) {result})'
    return result


def modules():
    artifact=json.loads((LEAN/'artifacts/setup/shift-binop.json').read_text())
    if [entry['id'] for entry in artifact['tables']]!=[0,3,4,6,7,8,9]:
        raise ValueError('Shift metadata scope changed')
    certificate=('import Airbender.Data.Tables.ShiftData\nimport Airbender.Proofs.Tables.FiniteGridChecks\n'+''.join(f'import Airbender.Proofs.GKRProtocol.ShiftPrefixNative.Column{lane}\n' for lane in range(10))+'\n'
        f'namespace {OWNER}\nset_option warningAsError true\nset_option Elab.async false\n'
        '-- Traverse the named region-part length corollaries.\nset_option maxRecDepth 8192\n\n'
        'def offsetsValue (kind : Fin 7) (_ : Fin 1) (_ : Fin 1) : Nat := (shiftData kind).offset\n\n'
        'theorem checked : FiniteGridChecks.check 7 1 1 offsetsValue (fun _ _ _ => 0) = true := by decide +kernel\n\n'
        'theorem offsets (kind : Fin 7) : (shiftData kind).offset = 0 :=\n'
        '  FiniteGridChecks.check_sound 7 1 1 offsetsValue (fun _ _ _ => 0) checked kind 0 0\n\nend '+OWNER+'\n')
    certificate=certificate[:certificate.rindex('end '+OWNER)]
    for lane in range(10):
        owner=f'Airbender.Compiler.ShiftPrefixNative.Column{lane}'
        _,chunks=plans(artifact,lane)
        checks=[f'{owner}.checkedRegion6Part{index}Length' for index,chunk in enumerate(chunks) if any(kind==6 for kind,_,_ in chunk[-1])]
        certificate+=(f'theorem shiftLength{lane} : ((byteShiftData.columns[({lane} : Nat)]).blocks.toList.map Airbender.Setup.Block.length).sum = 262144 := by\n'
                      f'  change (byteShiftColumn{lane}.blocks.toList.map Airbender.Setup.Block.length).sum = 262144\n'
                      f'  rw [{owner}.regionShape6]\n'
                      '  simp only [List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, '+', '.join(checks)+']\n  rfl\n\n')
    yield STEM+'.Certificate',certificate+'end '+OWNER+'\n'

    old=(LEAN/'Airbender/Proofs/Tables/ShiftColumnCoverage.lean').read_text()
    # Keep all public statement text and the general cast proof.
    first=old.index('theorem shift_coverage');cast=old.index('theorem native_cast')
    shift=old[first:old.index(' :=',first)]
    binary_start=old.index('theorem binary_coverage')
    binary=old[binary_start:binary_start+re.search(r' :=(?: by)?\n',old[binary_start:]).start()]
    if shift!=SHIFT or binary!=BINARY or old[cast:old.index(' :=',cast)]!=NATIVE:
        raise ValueError('original Shift metadata contracts changed')
    imports=old[:old.index('namespace Airbender')].replace(f'import {STEM}.Certificate\n','')
    imports=re.sub(r'^import Airbender.Proofs.GKRProtocol.ShiftPrefixNative.Column\d+\n','',imports,flags=re.M)
    source=f'import {STEM}.Certificate\n'+imports
    source=source.replace('import Mathlib.Tactic.FinCases\n','')
    source+='namespace Airbender.Verification.ShiftColumns\nopen Setup Setup.Proofs\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 131072\n\n'
    def fact(kind,lane):
        return f'{OWNER}.shiftLength{lane}' if kind==4 else f'Airbender.Compiler.ShiftPrefixNative.Column{lane}.regionLength{kind+2}'
    source+=shift+' :=\n  '+cases([fact(4,lane) for lane in range(10)],'((byteShiftData.columns[{index}]).blocks.toList.map Block.length).sum = 262144')+' lane\n\n'
    source+=binary+' :=\n  '+cases([cases([fact(kind,lane) for lane in range(10)],f'(({TABLES[kind]}.columns[{{index}}]).blocks.toList.map Block.length).sum = 65536') for kind in range(4)],'∀ lane : Fin 10, (((#v[byteXorData, byteOrData, byteAndData, byteTruncateData] : Vector (TableData 10) 4)[{index}]).columns[lane].blocks.toList.map Block.length).sum = 65536')+' kind lane\n\n'
    source+=old[cast:].replace('have offset : (shiftData kind).offset = 0 := by fin_cases kind <;> rfl',f'have offset : (shiftData kind).offset = 0 := {OWNER}.offsets kind')
    yield 'Airbender.Proofs.Tables.ShiftColumnCoverage',source
    binary_path=LEAN/'Airbender/Proofs/Tables/ImportedBinaryRows.lean'
    binary_rows=binary_path.read_text()
    begin=binary_rows.index('theorem coverage (kind : Fin 3)')
    end=binary_rows.index('private theorem output_get',begin)
    boundary=begin+re.search(r' :=(?: by)?\n',binary_rows[begin:]).start()
    if binary_rows[begin:boundary]!=OUTPUT_COVERAGE:
        raise ValueError('original binary output coverage contract changed')
    projection=cases([f'Airbender.Compiler.ShiftPrefixNative.Column2.regionLength{region}' for region in range(2,5)],
        '((data (binaryKind {index})).columns[2].blocks.toList.map Block.length).sum = 65536')
    binary_rows=binary_rows[:begin]+OUTPUT_COVERAGE+' :=\n  '+projection+' kind\n\n'+binary_rows[end:]
    dependency='import Airbender.Proofs.GKRProtocol.ShiftPrefixNative.Column2\n'
    if dependency not in binary_rows:binary_rows=dependency+binary_rows
    yield 'Airbender.Proofs.Tables.ImportedBinaryRows',binary_rows


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');parser.add_argument('--check',action='store_true')
    args=parser.parse_args();generated=list(modules())
    if args.write:preflight(generated)
    for name,source in generated:
        path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):raise ValueError('complete Shift metadata changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=source):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(name)


if __name__=='__main__':main()
