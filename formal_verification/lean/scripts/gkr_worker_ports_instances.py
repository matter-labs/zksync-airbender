#!/usr/bin/env python3
"""Bind actual worker RAM and virtual-CSR outputs to retained logical tokens."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN

FAMILIES = {'bigint': ('Bigint', 'Bigint', 'bigint'), 'blake-g': ('BlakeG', 'Blake2G', 'blakeG'),
            'blake-round': ('BlakeRound', 'Blake2Round', 'blakeRound'), 'keccak': ('Keccak', 'Keccak', 'keccak')}


def module(family, mode):
    stem, model, kind = FAMILIES[family]
    case = stem + mode.title()
    text = (LEAN / 'scripts/templates/gkr_worker_ports.lean').read_text()
    text = text.replace('BigintUncached', case).replace('Airbender.Bigint.', 'Airbender.' + model + '.')
    text = text.replace('.bigint, assignment', '.' + kind + ', assignment')
    stop = text.index('end Airbender.Compiler.WorkerPortsNative.')
    text = text[:stop]
    memory = f'Airbender.Compiler.MemoryNative.{case}.native'
    clean = f'Airbender.Compiler.CleanArithmeticNative.{case}.native'
    rows = f'({memory}.memoryReadRows ++ {memory}.memoryWriteRows)'
    assignment = f'({clean}.environment physical data).get'
    worker = f'(⟨.{kind}, {assignment}⟩ : Delegation.Row babyBearModulus)'
    for direction in ['read', 'write']:
        tokens = (f'Airbender.{model}.importedConstraintsMemoryPorts.toList.map (Trace.readToken {assignment})'
                  if direction == 'read' else f'Airbender.{model}.importedConstraintsMemoryPorts.toList.map ({worker}.writeToken)')
        marker = f'(Delegation.Requests.fulfillment {worker}).' + ('issued' if direction == 'read' else 'empty')
        logical = tokens + f' ++ [{marker}]'
        native_rows = memory + '.memory' + direction.title() + 'Rows'
        text += (f'theorem {direction}_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n'
                 f'    {native_rows}.map (fun row => row.token ({memory}.sourceValues physical)) =\n      {logical} := by\n'
                 f'  rw [← source_{direction}_tokens {assignment} ({memory}.sourceValues physical)]\n'
                 '  apply List.map_congr_left\n  intro row member\n  apply row_token_from_base\n'
                 f'  exact List.mem_append_{"left" if direction == "read" else "right"} _ member\n\n')
        text += (f'theorem {direction}_products_from_base {{R : Type}} [CommRing R]\n'
                 '    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)\n'
                 '    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :\n'
                 f'    ({native_rows}.map (fun row => row.fingerprint ({memory}.sourceValues physical) hom challenges)).prod =\n'
                 f'      (({logical}).map (memoryTokenFingerprint hom challenges)).prod := by\n'
                 f'  rw [← Source.MemoryRow.token_products {native_rows} ({memory}.sourceValues physical) hom challenges,\n'
                 f'    {direction}_tokens_from_base physical data]\n\n')
    # The checked native product-reduction argument is identical to the executor
    # case. Replace only the retained token view and its physical binding lemma.
    executor = (LEAN / 'Airbender/Proofs/GKRProtocol/MemoryPortsNative/AddSubUncached.lean').read_text()
    executor = executor.replace('AddSubUncached', case).replace('Airbender.AddSub.', 'Airbender.'+model+'.')
    output = executor[executor.index('theorem read_output_logical'):executor.index('\nend Airbender.Compiler.MemoryPortsNative.')]
    for direction, point in [('read','initial'),('write','final')]:
        start = output.index('theorem ' + direction + '_output_logical')
        stop = output.find('theorem write_output_logical', start + 1) if direction=='read' else len(output)
        block = output[start:stop]
        token_start = block.index('      ((Airbender.')
        token_stop = block.index(').map\n        (memoryTokenFingerprint', token_start)
        if direction=='read':
            tokens=f'Airbender.{model}.importedConstraintsMemoryPorts.toList.map (Trace.readToken {assignment})'
            marker='issued'
        else:
            tokens=f'Airbender.{model}.importedConstraintsMemoryPorts.toList.map ({worker}.writeToken)'
            marker='empty'
        block=block[:token_start]+'      (('+tokens+f' ++ [(Delegation.Requests.fulfillment {worker}).{marker}]'+block[token_stop:]
        block=block.replace(f'Airbender.{model}.importedConstraintsTraceColumns.execute', f'Airbender.{model}.importedConstraintsDelegationColumns.execute')
        block=block.replace('(original_assignment physical data 4 (by decide +kernel)).symm', 'original_assignment physical data 0 (List.mem_append_left _ (List.mem_cons_self))')
        if direction=='read':read_output=block
        else:write_output=block
    text += read_output + write_output
    text += f'\nend Airbender.Compiler.WorkerPortsNative.{case}\n'
    text = text.replace('import Airbender.Proofs.GKRProtocol.MemoryTokens\n',
                        f'import Airbender.Proofs.GKRProtocol.MemoryTokens\nimport Airbender.Proofs.GKRProtocol.FunctionalLinksNative.{case}\nimport Airbender.Proofs.GKRProtocol.NativeWitness\n')
    return 'Airbender.Proofs.GKRProtocol.WorkerPortsNative.' + case, text


def modules(family, mode):
    target,text=module(family,mode)
    if family!='blake-round':
        yield target,text
        return
    stem,model,_=FAMILIES[family];case=stem+mode.title()
    pair=json.loads((LEAN/'artifacts/compiler'/f'{family}-{mode}.json').read_text())
    size=len(pair['circuit']['memory_layout']['ram_access_sets'])
    namespace='Airbender.Compiler.WorkerPortsNative.'+case
    a=text.index('theorem history_columns');b=text.index('noncomputable def logicalValues',a)
    statement=text[a:b]
    relation=statement[statement.index('(fun index =>')+1:statement.index('))) = true := by decide +kernel')]
    # The extracted relation includes the outer lambda and its inner all check.
    relation=relation+')'
    shared='Airbender.Proofs.GKRProtocol.WorkerPortsParts.'+case+'.Shared'
    prefix=text[:a]+f'noncomputable def historyPredicate : Fin Airbender.{model}.importedConstraintsMemoryPorts.size → Bool := '+relation+'\n\nend '+namespace+'\n'
    yield shared,prefix
    parts=[]
    for first in range(0,size,4):
        stop=min(first+4,size);part='Airbender.Proofs.GKRProtocol.WorkerPortsParts.'+case+'.Part'+str(first//4)
        parts.append(part)
        body=(f'import {shared}\nimport Airbender.Import.GKRProtocol.WorkerPortsChecks\n\nnamespace {namespace}\n'
              'open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\n'
              'set_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
              f'worker_checks_part historyPart{first} input_list (List.finRange Airbender.{model}.importedConstraintsMemoryPorts.size)\n'
              f'  test_fn historyPredicate start {first} stop {stop}\n\nend {namespace}\n')
        yield part,body
    blocks=[f'historyPart{first}Block' for first in range(0,size,4)]
    checks='BoolChecks.nil'
    for first in reversed(range(0,size,4)):
        checks=f'BoolChecks.cons historyPart{first} ({checks})'
    aggregate=(f'theorem history_columns : (List.finRange Airbender.{model}.importedConstraintsMemoryPorts.size).all historyPredicate = true := by\n'
               '  have coverage : (['+', '.join(blocks)+f'] : List (List (Fin Airbender.{model}.importedConstraintsMemoryPorts.size))).flatten = List.finRange Airbender.{model}.importedConstraintsMemoryPorts.size := by rfl\n'
               '  rw [← coverage]\n  apply QueryFrameImport.all_flatten_true\n'
               f'  exact BoolChecks.all_true (predicate := fun block : List (Fin Airbender.{model}.importedConstraintsMemoryPorts.size) => block.all historyPredicate) (items := [{", ".join(blocks)}]) ({checks})\n\n')
    header=''.join('import '+part+'\n' for part in parts)+f'\nnamespace {namespace}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    yield target,header+aggregate+text[b:]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family',choices=FAMILIES,action='append')
    p.add_argument('--mode',choices=['cached','uncached'],action='append')
    for flag in ['write','check','build']:p.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    for family in a.family or FAMILIES:
        for mode in a.mode or ['uncached','cached']:
            for target,text in modules(family,mode):
                path=LEAN/(target.replace('.','/')+'.lean')
                if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('worker token proof changed: '+target)
                if a.write:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
                print(target,flush=True)
                if a.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
