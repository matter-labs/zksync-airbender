"""Render complete memory-frame bindings with bounded exact source windows."""
import json
import re
from export_gkr_translations import LEAN
from gkr_full_arithmetic_certificate import synthesize
from gkr_packed_query_frame import capture_name, merge_slices


def capture_shape(case):
    name=capture_name(case)
    root=LEAN/'artifacts/compiler'
    arithmetic=synthesize(json.loads((root/(name+'.json')).read_text()),json.loads((root/(name+'-source.json')).read_text()))
    text=(LEAN/'Airbender/Proofs/GKRProtocol/MemoryNative'/(case+'.lean')).read_text()
    native=json.loads(json.loads(re.search(r'selectors ("(?:[^"\\]|\\.)*")',text)[1]))
    inputs=len(arithmetic['inputs']);arity=len(native['addresses'])
    if native['addresses'][:inputs]!=arithmetic['inputs']:
        raise ValueError('memory input prefix changed: '+case)
    size=7*sum(len(native['groups'][stem]['source_labels']) for stem in ['memoryRead','memoryWrite'])
    return inputs,arity,size


def modules(case, original_source, certificate):
    inputs,arity,ram_count=capture_shape(case)
    stem='Airbender.Proofs.GKRProtocol.MemoryFrameChecks.'+case
    owner='Airbender.Compiler.MemoryFrameChecks.'+case
    base='Airbender.Compiler.FullArithmeticNative.'+case+'.native'
    mem='Airbender.Compiler.MemoryNative.'+case+'.native'
    native='Airbender.Compiler.MemoryFrameNative.'+case+'.native'
    header=f'namespace {owner}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 8192\n\n'
    end='\nend '+owner+'\n'
    generated=[]
    def emit(role,text):generated.append((stem+'.'+role,text))
    emit('PrefixBindings',f'''import Airbender.Proofs.GKRProtocol.MemoryFrameNative.{case}Inputs
import Airbender.Proofs.GKRProtocol.NumericMemoryFramePrefix
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport
namespace Airbender.Compiler.MemoryFrameChecks.{case}
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192
numeric_data_binding memory_inputPrefix : Airbender.Compiler.MemoryNative.{case}.native.addresses.take Airbender.Compiler.FullArithmeticNative.{case}.native.inputs.length = Airbender.Compiler.FullArithmeticNative.{case}.native.inputs

theorem inputCoordinates (wire : Fin {arity}) (inside : wire.val < {inputs}) :
    Airbender.Compiler.MemoryNative.{case}.native.bank.address wire = Airbender.Compiler.FullArithmeticNative.{case}.native.inputBank.address ⟨wire.val, inside⟩ :=
  NumericMemoryFrameChecks.address_getter_prefix Airbender.Compiler.MemoryNative.{case}.native.addresses Airbender.Compiler.FullArithmeticNative.{case}.native.inputs
    (by decide) memory_inputPrefix ⟨wire.val, inside⟩

theorem inputRoundTrip (wire : Fin {inputs}) :
    Airbender.Compiler.FullArithmeticNative.{case}.native.inputBank.placement (Airbender.Compiler.FullArithmeticNative.{case}.native.inputBank.address wire) = wire := by
  apply WireBank.ofList_roundTrip
  rw [← Airbender.Compiler.FullArithmeticNative.{case}.native.inputPrefix]
  exact Airbender.Compiler.FullArithmeticNative.{case}.native.addressesUnique.take
end Airbender.Compiler.MemoryFrameChecks.{case}
''')
    emit('Data',f'import {stem}.PrefixBindings\nimport Airbender.Import.GKRProtocol.NumericMemoryFrameImport\n\n'+header+
        'set_option exponentiation.threshold 4096 in\nset_option maxHeartbeats 2000000 in\n'+
        'numeric_memory_frame_capture data := '+original_source.replace('NumericMemoryFrameChecks.ofTyped ', 'NumericMemoryFrameChecks.ofTypedPrefix ')+end)
    common=f'import {stem}.Data\nimport Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'
    source_functions=[('placement',f'(fun wire : Fin {arity} => if wire.val < {inputs} then wire.val else ({base}.inputBank.placement ({mem}.bank.address wire)).val)'),('nativeAddress',f'(fun wire : Fin {arity} => AddressUniqueChecks.addressCode ({mem}.bank.address wire))'),('inputAddress',f'(fun wire : Fin {arity} => if wire.val < {inputs} then AddressUniqueChecks.addressCode ({mem}.bank.address wire) else AddressUniqueChecks.addressCode ({base}.inputBank.address ({base}.inputBank.placement ({mem}.bank.address wire))))'),('fullAddress',f'(fun wire : Fin {arity} => if wire.val < {inputs} then AddressUniqueChecks.addressCode ({mem}.bank.address wire) else AddressUniqueChecks.addressCode ({base}.bank.address ({base}.bank.placement ({mem}.bank.address wire))))')]
    for name,function in source_functions:
        lines=[f'noncomputable def {name}Source : Fin {arity} → Nat := {function}\n'];leaves=[];values=f'data.{name}.toList';original=f'(List.ofFn {name}Source)'
        for first in range(0,arity,32):
            size=min(32,arity-first);leaf=f'{name}Leaf{first}';sl=f'{name}Slice{first}'
            lines.append(f'numeric_data_binding {leaf} : ({values}.drop {first}).take {size} =\n  NumericQueryFrameChecks.window {name}Source {first} {size} (by decide +kernel)\n')
            lines.append(f'theorem {sl} : ({values}.drop {first}).take {size} = ({original}.drop {first}).take {size} :=\n  {leaf}.trans (NumericQueryFrameChecks.window_binding {name}Source {first} {size} (by decide +kernel))\n');leaves.append((sl,size))
        assembled=merge_slices(name,values,original,0,arity,leaves,lines)
        lines.append(f'theorem {name}_fast_binding : {values} = {original} :=\n  NumericQueryFrameChecks.complete_binding {values} {original} {arity}\n    (by decide +kernel) List.length_ofFn {assembled}\n')
        emit(name[0].upper()+name[1:]+'Bindings',common+header+'\n'.join(lines)+end)
    encode=f'(fun field : Source.MemoryField => NumericPolynomialChecks.encode (field.polynomial {mem}.sourcePlacement))'
    lines=[f'noncomputable def encodeField : Source.MemoryField → NumericPolynomialChecks.Data := {encode}\n',f'noncomputable def ramSource := {native}.ramFields.map encodeField\n'];leaves=[];values='data.ram';original='ramSource'
    for first in range(0,ram_count,16):
        size=min(16,ram_count-first);leaf=f'ramLeaf{first}';sl=f'ramSlice{first}'
        lines.append(f'numeric_data_binding {leaf} : ({values}.drop {first}).take {size} =\n  (({native}.ramFields.drop {first}).take {size}).map encodeField\n')
        lines.append(f'theorem {sl} : ({values}.drop {first}).take {size} = ({original}.drop {first}).take {size} :=\n  {leaf}.trans (NumericQueryFrameChecks.map_window {native}.ramFields encodeField {first} {size})\n');leaves.append((sl,size))
    assembled=merge_slices('ram',values,original,0,ram_count,leaves,lines)
    lines.append(f'theorem ramLength : {native}.ramFields.length = {ram_count} := by decide +kernel\n')
    lines.append(f'theorem ram_binding : {values} = {original} :=\n  NumericQueryFrameChecks.complete_binding {values} {original} {ram_count}\n    (by decide +kernel) (by rw [ramSource, List.length_map, ramLength]) {assembled}\n')
    for field,old in [('initialization','initializationFields'),('execution','executeFields')]:
        lines.append(f'numeric_data_binding {field}_binding : data.{field} = {native}.{old}.map encodeField\n')
    emit('FieldsBindings',common+header+'\n'.join(lines)+end)
    args=original_source.removeprefix('NumericMemoryFrameChecks.ofTyped ')
    lines=[f'numeric_data_binding active_binding : data.activeMask = NumericQueryFrameChecks.coordinateMask ({native}.activeCoordinates.map Fin.val)\n',f'numeric_data_binding all_binding : data.allMask = NumericQueryFrameChecks.coordinateMask ({native}.allCoordinates.map Fin.val)\n']
    for field,actual in [('placement',f'List.ofFn (fun wire => ({base}.inputBank.placement ({mem}.bank.address wire)).val)'),('inputAddress',f'List.ofFn (fun wire => AddressUniqueChecks.addressCode ({base}.inputBank.address ({base}.inputBank.placement ({mem}.bank.address wire))))'),('fullAddress',f'List.ofFn (fun wire => AddressUniqueChecks.addressCode ({base}.bank.address ({base}.bank.placement ({mem}.bank.address wire))))')]:
        lines.append(f'theorem {field}_binding : data.{field}.toList = {actual} := by\n  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.{field}.toList)\n    (NumericMemoryFrameChecks.ofTypedPrefix_eq {args}\n      inputCoordinates inputRoundTrip {base}.artifact.projection {base}.inputCoordinates {base}.bankRoundTrip)\n  have bound : List.ofFn {field}Source = {actual} := by\n    unfold {field}Source\n    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same\n  exact {field}_fast_binding.trans bound\n')
    lines.append(f'theorem nativeAddress_binding : data.nativeAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode ({mem}.bank.address wire)) := nativeAddress_fast_binding\n')
    imports=''.join(f'import {stem}.{role}Bindings\n' for role in ['Placement','NativeAddress','InputAddress','FullAddress','Fields'])
    emit('Bindings',imports+'\n'+header+'\n'.join(lines)+end)
    emit('Certificate',certificate.replace('NumericMemoryFrameChecks.check_sound_of_binding','NumericMemoryFrameChecks.check_sound').replace('source_binding checked','active_binding all_binding placement_binding nativeAddress_binding inputAddress_binding fullAddress_binding ram_binding initialization_binding execution_binding checked'))
    return generated
