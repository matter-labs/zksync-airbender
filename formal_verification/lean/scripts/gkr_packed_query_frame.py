#!/usr/bin/env python3
"""Check complete query-frame captures after exact numeric source binding."""
import argparse
from export_gkr_translations import LEAN
from gkr_packed_rotate_boundary import preflight

from gkr_wiring_instances import CASES as CIRCUIT_CASES

LARGE_CASES=tuple(stem+mode for stem in CIRCUIT_CASES if stem!='AddSub' for mode in ['Cached'])
MATERIALIZATION_BUDGET_CASES=('BlakeRoundCached',)
CASES=('AddSubCached',)+LARGE_CASES


def source(case):
    prefix='Airbender.Compiler.'
    original=prefix+'QueryFrameNative.'+case+'.native'
    base=prefix+'FullArithmeticNative.'+case+'.native'
    lookup=prefix+'LookupNative.'+case+'.native'
    queries=prefix+'LookupSourceNative.'+case+'.native'
    return (f'NumericQueryFrameChecks.ofTyped {original}.fields {original}.coordinates\n'
            f'  {base}.originalProjection {lookup}.sourcePlacement {base}.inputBank {queries}.bank')


def small_modules(case):
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


def capture_name(case):
    from export_gkr_translations import FAMILIES
    family=next(family for family,stem in zip(FAMILIES,CIRCUIT_CASES,strict=True) if case == stem+'Cached')
    return family+'-cached'


def capture_shape(case):
    import json
    payload=json.loads((LEAN/'artifacts/compiler/lookup'/(capture_name(case)+'.json')).read_text())
    return len(payload['addresses']),sum(len(row['fields']) for row in payload['rows'])


def merge_slices(prefix,values,source,first,count,leaves,lines):
    if len(leaves)==1:return leaves[0][0]
    middle=len(leaves)//2;left=leaves[:middle];right=leaves[middle:]
    left_count=sum(item[1] for item in left);right_count=count-left_count
    first_proof=merge_slices(prefix,values,source,first,left_count,left,lines)
    second_proof=merge_slices(prefix,values,source,first+left_count,right_count,right,lines)
    name=f'{prefix}Node{first}_{count}'
    lines.append(f'theorem {name} : ({values}.drop {first}).take {count} = ({source}.drop {first}).take {count} :=\n'
        f'  NumericQueryFrameChecks.merge_bindings {values} {source} {first} {left_count} {right_count} {first_proof} {second_proof}\n')
    return name


def large_modules(case):
    arity,size=capture_shape(case)
    stem='Airbender.Proofs.GKRProtocol.QueryFrameChecks.'+case
    owner='Airbender.Compiler.QueryFrameChecks.'+case
    native='Airbender.Compiler.QueryFrameNative.'+case+'.native'
    base='Airbender.Compiler.FullArithmeticNative.'+case+'.native'
    lookup='Airbender.Compiler.LookupNative.'+case+'.native'
    bank='Airbender.Compiler.LookupSourceNative.'+case+'.native.bank'
    header=(f'namespace {owner}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\n'
        'set_option Elab.async false\nset_option maxRecDepth 8192\n\n')
    end='\nend '+owner+'\n'
    binding_imports=(f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n')
    yield stem+'.Data',(f'import Airbender.Proofs.GKRProtocol.QueryFrameNative.{case}Inputs\n'
        'import Airbender.Import.GKRProtocol.NumericQueryFrameImport\n\n'+header+
        ('set_option maxHeartbeats 2000000 in\n' if case in MATERIALIZATION_BUDGET_CASES else '')+
        'numeric_query_frame_capture data := '+source(case)+end)
    sources=[('placement',f'(fun wire : Fin {arity} => ({base}.inputBank.placement ({bank}.address wire)).val)'),
        ('nativeAddress',f'(fun wire : Fin {arity} => AddressUniqueChecks.addressCode ({bank}.address wire))'),
        ('returnedAddress',f'(fun wire : Fin {arity} => AddressUniqueChecks.addressCode ({base}.inputBank.address ({base}.inputBank.placement ({bank}.address wire))))')]
    for name,function in sources:
        lines=[f'noncomputable def {name}Source : Fin {arity} → Nat := {function}\n']
        leaves=[];values=f'data.{name}';original=f'(List.ofFn {name}Source)'
        for first in range(0,arity,32):
            count=min(32,arity-first);leaf=f'{name}Leaf{first}';slice_name=f'{name}Slice{first}'
            lines.append(f'numeric_data_binding {leaf} : ({values}.drop {first}).take {count} =\n'
                f'  NumericQueryFrameChecks.window {name}Source {first} {count} (by decide +kernel)\n')
            lines.append(f'theorem {slice_name} : ({values}.drop {first}).take {count} = ({original}.drop {first}).take {count} :=\n'
                f'  {leaf}.trans (NumericQueryFrameChecks.window_binding {name}Source {first} {count} (by decide +kernel))\n')
            leaves.append((slice_name,count))
        assembled=merge_slices(name,values,original,0,arity,leaves,lines)
        lines.append(f'theorem {name}_binding : {values} = {original} :=\n'
            f'  NumericQueryFrameChecks.complete_binding {values} {original} {arity}\n'
            f'    (by decide +kernel) (List.length_ofFn) {assembled}\n')
        yield stem+'.'+name[0].upper()+name[1:]+'Bindings',binding_imports+header+'\n'.join(lines)+end
    encode=(f'(fun field : Source.EncodedField => (NumericPolynomialChecks.encode (field.polynomial {base}.originalProjection), '
        f'NumericPolynomialChecks.encode (field.polynomial {lookup}.sourcePlacement)))')
    lines=[f'noncomputable def encodeField : Source.EncodedField → NumericPolynomialChecks.Data × NumericPolynomialChecks.Data := {encode}\n',
        f'noncomputable def fieldsSource := {native}.fields.map encodeField\n']
    leaves=[];original='fieldsSource';values='data.fields'
    for first in range(0,size,16):
        count=min(16,size-first);leaf=f'fieldsLeaf{first}';slice_name=f'fieldsSlice{first}'
        lines.append(f'numeric_data_binding {leaf} : ({values}.drop {first}).take {count} =\n'
            f'  (({native}.fields.drop {first}).take {count}).map encodeField\n')
        lines.append(f'theorem {slice_name} : ({values}.drop {first}).take {count} = ({original}.drop {first}).take {count} :=\n'
            f'  {leaf}.trans (NumericQueryFrameChecks.map_window {native}.fields encodeField {first} {count})\n')
        leaves.append((slice_name,count))
    assembled=merge_slices('fields',values,original,0,size,leaves,lines)
    lines.append(f'theorem originalFieldsLength : {native}.fields.length = {size} := by decide +kernel\n')
    lines.append(f'theorem fields_binding : {values} = {original} :=\n'
        f'  NumericQueryFrameChecks.complete_binding {values} {original} {size}\n'
        f'    (by decide +kernel) (by rw [fieldsSource, List.length_map, originalFieldsLength]) {assembled}\n')
    yield stem+'.FieldsBindings',binding_imports+header+'\n'.join(lines)+end
    imports=''.join(f'import {stem}.{role}Bindings\n' for role in ['Placement','NativeAddress','ReturnedAddress','Fields'])
    yield stem+'.Bindings',imports+'\n'+header+f'numeric_data_binding coordinates_binding : data.coordinates = {native}.coordinates.map Fin.val\n'+end
    yield stem+'.IndexedData',(f'import {stem}.Data\nimport Airbender.Import.GKRProtocol.NumericQueryFrameIndexImport\n'
        'import Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header+
        'set_option exponentiation.threshold 4096 in\nnumeric_query_frame_index views := NumericQueryFrameChecks.index data\n'
        'numeric_data_binding coordinates_index_binding : views.coordinates = NumericQueryFrameChecks.coordinateMask data.coordinates\n'
        'numeric_data_binding placement_index_binding : views.placement.toList = data.placement\n'
        'numeric_data_binding nativeAddress_index_binding : views.nativeAddress.toList = data.nativeAddress\n'
        'numeric_data_binding returnedAddress_index_binding : views.returnedAddress.toList = data.returnedAddress\n'+end)
    yield stem+'.Certificate',(f'import {stem}.Bindings\nimport {stem}.IndexedData\n\n'+header+
        'theorem indexedChecked : NumericQueryFrameChecks.indexedCheck views data.fields = true := by decide +kernel\n\n'
        'theorem checked : NumericQueryFrameChecks.check data = true :=\n'
        '  NumericQueryFrameChecks.indexedCheck_sound views data coordinates_index_binding\n'
        '    placement_index_binding nativeAddress_index_binding returnedAddress_index_binding indexedChecked\n\n'
        f'theorem originalChecked : {native}.fields.all (fun field =>\n'
        f'    erasureUntouched {native}.coordinates (field.polynomial {base}.originalProjection) &&\n'
        f'      field.transportCheck {base}.originalProjection {lookup}.sourcePlacement\n'
        f'        {base}.inputBank {bank}) = true :=\n'
        f'  NumericQueryFrameChecks.check_sound data {native}.fields {native}.coordinates\n'
        f'    {base}.originalProjection {lookup}.sourcePlacement {base}.inputBank {bank}\n'
        '    coordinates_binding placement_binding nativeAddress_binding returnedAddress_binding fields_binding checked\n'+end)


def modules(case):
    yield from large_modules(case) if case in LARGE_CASES else small_modules(case)


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
