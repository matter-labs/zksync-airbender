#!/usr/bin/env python3
"""Plan actual unified block/region correspondences; Lean checks remain separate."""
import json
from collections import Counter
from export_gkr_translations import LEAN
from gkr_rom_columns import length

PREFIX=2097537
CHUNK=128


def value(block,index):
    if block['kind']=='affine':return block['first']+block['step']*index
    if block['kind']=='dense':return block['values'][index]
    return block['values'][index%len(block['values'])]+block['stride']*(index//len(block['values']))


def slice_block(block,start,count):
    if start==0 and count==length(block):return [(start,block)]
    if block['kind']=='affine':return [(start,dict(kind='affine',length=count,first=value(block,start),step=block['step']))]
    if block['kind']=='dense':return [(start,dict(kind='dense',values=block['values'][start:start+count]))]
    period=len(block['values']);leading=min(count,(period-start%period)%period)
    cycles=(count-leading)//period;trailing=(count-leading)%period;out=[]
    if leading:out.append((start,dict(kind='dense',values=[value(block,start+i) for i in range(leading)])))
    if cycles:
        out.append((start+leading,dict(kind='periodic',repetitions=cycles,stride=block['stride'],values=[value(block,start+leading+i) for i in range(period)])))
    if trailing:
        pos=start+leading+cycles*period
        out.append((pos,dict(kind='dense',values=[value(block,pos+i) for i in range(trailing)])))
    return out


def mode(source,target,offset):
    if offset==0 and source==target:return 'identical'
    if source['kind']==target['kind']=='affine' and source['step']==target['step'] and value(source,offset)==target['first']:
        return 'affine'
    if source['kind']==target['kind']=='periodic' and source['stride']==target['stride']==0 and source['values']==target['values'] and offset%len(source['values'])==0:
        return 'periodic'
    if length(target)<=256:return 'finite'
    return 'unsupported'


def plans(column):
    artifact=json.loads((LEAN/'artifacts/setup/unified.json').read_text())
    blocks=artifact['columns'][column]['blocks'];positions=[0]
    for block in blocks:positions.append(positions[-1]+length(block))
    stop=next(i for i,p in enumerate(positions) if p>=PREFIX)
    groups=[[] for _ in range(stop)]
    regions=[]
    for r,region in enumerate(artifact['tables']):
        lo=region['offset'];hi=lo+region['length'];selected=[]
        for i,block in enumerate(blocks[:stop]):
            a=max(lo,positions[i]);b=min(hi,positions[i+1])
            if a>=b:continue
            for offset,target in slice_block(block,a-positions[i],b-a):
                entry=dict(source=i,offset=offset,block=target,region=r,target=len(selected),mode=mode(block,target,offset))
                selected.append(entry);groups[i].append(entry)
        regions.append(selected)
    extra=positions[stop]-PREFIX
    if extra:
        i=stop-1;offset=PREFIX-positions[i]
        target=dict(kind='dense',values=[value(blocks[i],offset+j) for j in range(extra)])
        groups[i].append(dict(source=i,offset=offset,block=target,region=None,target=0,mode=mode(blocks[i],target,offset)))
    assert all(sum(length(e['block']) for e in group)==length(blocks[i]) for i,group in enumerate(groups))
    assert all([e['offset'] for e in group]==[sum(length(x['block']) for x in group[:j]) for j in range(len(group))] for group in groups)
    return artifact,blocks,positions,stop,groups,regions


def print_plan():
    for col in range(10):
        artifact,blocks,positions,stop,groups,regions=plans(col)
        counts=Counter(e['mode'] for group in groups for e in group)
        changed=sum(any(e['mode']!='identical' for group in groups[a:a+CHUNK] for e in group) for a in range(0,stop,CHUNK))
        print(col,'blocks',stop,'fragments',sum(counts.values()),'modes',dict(counts),'changed_chunks',changed)
        for i,group in enumerate(groups):
            for e in group:
                if e['mode']=='unsupported':print('unsupported',i,e['region'],e['target'],e['offset'],length(e['block']),blocks[i]['kind'],e['block']['kind'])

DATA={0:'nativeZeroData',1:'nativeRegisterZeroData',2:'nativeCleanupData',3:'nativeByteSignData',5:'nativeSignData',8:'nativeTruncationData',9:'nativeShiftData',34:'nativeROMData',47:'nativeRotate16Data',48:'nativeRotate12Data',49:'nativeRotate8Data',50:'nativeRotate7Data',51:'nativeConditionalData',52:'nativeXorData',53:'nativeOrData',54:'nativeAndData'}


def nat_array(values):return '#['+', '.join(map(str,values))+']'


def int_term(value):return str(value) if value>=0 else '('+str(value)+')'


def affine_term(block):return f'(Setup.Block.affine {block["length"]} {block["first"]} {int_term(block["step"])})'


def span_proof(source,target,offset,kind,src,dst,legacy_finite=False):
    count=length(target)
    text='intro index bounded\n'
    text+=f'change {src}.get? ({offset} + index) = {dst}.get? index\n'
    if kind=='identical':
        text+=f'have same : {src} = {dst} := by rfl\nrw [same, Nat.zero_add]\n'
    elif kind=='affine':
        text+=f'change {affine_term(source)}.get? ({offset} + index) = {affine_term(target)}.get? index\n'
        text+='apply affine_block_span\n'
        text+=f'· exact (by have bound : index < {count} := bounded; omega : {offset} + index < {length(source)})\n'
        text+=f'· exact (show index < {count} from bounded)\n· decide +kernel\n'
    elif kind=='periodic':
        values=nat_array(source['values']);period=len(source['values'])
        text+=f'change (Setup.Block.periodic {source["repetitions"]} 0 {values}).get? ({offset} + index) =\n  (Setup.Block.periodic {target["repetitions"]} 0 {values}).get? index\n'
        text+='apply periodic_zero_block_span\n'
        text+=f'· exact (by have bound : index < {count} := bounded; omega : {offset} + index < {length(source)})\n'
        text+=f'· exact (show index < {count} from bounded)\n'
        text+=f'· exact (by decide +kernel : {offset} % {period} = 0)\n'
    elif kind=='finite':
        if legacy_finite:
            text+=f'have checked : finiteBlockSpanCheck {src} {dst} {offset} {count} = true := by decide +kernel\n'
            text+=f'exact finite_block_span_sound {src} {dst} {offset} {count} checked index (show index < {count} from bounded)\n'
        elif count<=32:
            text+=f'have checked : finiteBlockSpanRangeCheck {src} {dst} {offset} 0 {count} = true := by decide +kernel\n'
            text+=f'exact finite_block_span_range_sound {src} {dst} {offset} 0 {count} checked index (by omega) (by have : index < {count} := bounded; omega)\n'
        else:
            ranges=[(start,min(32,count-start)) for start in range(0,count,32)]
            for start,size in ranges:
                text+=f'have checked{start} : finiteBlockSpanRangeCheck {src} {dst} {offset} {start} {size} = true := by decide +kernel\n'
            indent=''
            for j,(start,size) in enumerate(ranges):
                if j<len(ranges)-1:
                    text+=indent+f'by_cases before{start} : index < {start+size}\n'+indent+'· '
                    stepindent=indent+'  '
                else:
                    text+=indent;stepindent=indent
                text+=f'exact finite_block_span_range_sound {src} {dst} {offset} {start} {size} checked{start} index (by omega) (by have : index < {count} := bounded; omega)\n'
                if j<len(ranges)-1:text+=indent+'·\n';indent+='  '
    else:raise ValueError('unsupported actual span')
    return text


def pilot(column=1, begin=0, end=None, assemble=True, source_start=0, source_end=None, namespace=None, foundation_module=None):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    if source_end is None:source_end=stop
    assert source_end-source_start<=CHUNK,'one bounded source chunk per module foundation'
    ns=namespace or f'Airbender.Compiler.UnifiedPrefixNative.Column{column}'
    full=f'Data.GKRSetup.Unified.setupColumn{column}'
    text=('import Airbender.Proofs.GKRProtocol.BlockSpans\nimport Airbender.Import.GKRProtocol.BlockCoverageImport\nimport Airbender.Data.GKRSetup.Unified\n'
      'import Airbender.Review.Circuits.UnifiedReduced.Tables.NativeFixedData\nimport Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ROMData\n\nnamespace '+ns+'\n'
      'open Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n')
    source_header=f'column_blocks_part original from {full} start {source_start} stop {source_end}\ncolumn_blocks_part suffix from {full} start {source_end} stop {len(blocks)}\n\n'
    if assemble:text+=source_header
    else:
        dependency=foundation_module or f'Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column{column}.Foundation'
        text=f'import {dependency}\n\nnamespace {ns}\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'

    if end is None:end=stop
    for i in range(begin,end):
        group=groups[i]
        src=f'source{i}'
        text+=f'noncomputable def {src} : Setup.Block := original.get ⟨{i-source_start}, by decide +kernel⟩\n\n'
        names=[]
        for j,e in enumerate(group):
            part=f'part{i}_{j}';dst=f'destination{i}_{j}';names.append(part)
            if e['region'] is None:
                text+=f'noncomputable def {part} : List Setup.Block := [.dense {nat_array(e["block"]["values"])}]\n'
            else:
                region=artifact['tables'][e['region']];owner=DATA[region['id']]
                text+=f'column_blocks_part {part} from (UnifiedReduced.Setup.{owner}.columns[({column} : Nat)]) start {e["target"]} stop {e["target"]+1}\n'
            text+=f'noncomputable def {dst} : Setup.Block := {part}.get ⟨0, by decide +kernel⟩\n\n'
        text+=f'noncomputable def target{i} : List Setup.Block := '+' ++ '.join(names)+'\n\n'
        proofs=[]
        for j,e in enumerate(group):
            body=span_proof(blocks[i],e['block'],e['offset'],e['mode'],src,f'destination{i}_{j}',legacy_finite=column==1 and namespace is None and i<8)
            proofs.append('(by\n'+''.join('    '+line+'\n' for line in body.splitlines())+'  )')
        proof='True.intro'
        for p in reversed(proofs):proof=f'And.intro {p} ({proof})'
        if i in [14,33]:text+='set_option maxHeartbeats 16000000 in\n'
        text+=f'theorem follows{i} : blockTargetsFollow {src} 0 target{i} :=\n  {proof}\n\n'
        text+=f'theorem length{i} : (target{i}.map Setup.Block.length).sum = {src}.length := by decide +kernel\n\n'
    if not assemble:
        text+='end '+ns+'\n'
        return f'Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column{column}.Part{begin//8}',text
    text+='noncomputable def sources : List Setup.Block := ['+', '.join(f'source{i}' for i in range(stop))+']\n\n'
    text+='noncomputable def targets : List (List Setup.Block) := ['+', '.join(f'target{i}' for i in range(stop))+']\n\n'
    text+='theorem sourcesAgree : original = sources := by rfl\n\n'
    proof='List.Forall₂.nil'
    for i in reversed(range(stop)):proof=f'List.Forall₂.cons (⟨length{i}, follows{i}⟩) ({proof})'
    text+='theorem spansChecked : List.Forall₂ (fun source target => (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets :=\n  '+proof+'\n\n'
    text+='theorem span_value (index : Nat) : Setup.getFromBlocks original index = Setup.getFromBlocks targets.flatten index := by\n  rw [sourcesAgree]\n  exact block_partitions_agree sources targets spansChecked index\n\nend '+ns+'\n'
    return f'Airbender.Proofs.GKRProtocol.UnifiedPrefixNative.Column{column}',text


def pilot_assembly(column=1):
    artifact,blocks,positions,stop,groups,regions=plans(column)
    assert stop<=CHUNK
    ns=f'Airbender.Compiler.UnifiedPrefixNative.Column{column}';full=f'Data.GKRSetup.Unified.setupColumn{column}'
    text=f'import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column{column}.Part0\n'+''.join(f'import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column{column}.Unit{i}\n' for i in range(8,stop))
    text+='\nnamespace '+ns+'\nopen Airbender Airbender.Compiler\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    text+='noncomputable def sources : List Setup.Block := ['+', '.join(f'source{i}' for i in range(stop))+']\n\n'
    text+='noncomputable def targets : List (List Setup.Block) := ['+', '.join(f'target{i}' for i in range(stop))+']\n\n'
    text+='theorem sourcesAgree : original = sources := by rfl\n\n'
    proof='List.Forall₂.nil'
    for i in reversed(range(stop)):proof=f'List.Forall₂.cons (⟨length{i}, follows{i}⟩) ({proof})'
    text+='theorem spansChecked : List.Forall₂ (fun source target => (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets :=\n  '+proof+'\n\n'
    text+=f'column_parts_cover sourceCoverage from {full} parts [original, suffix]\n\n'
    text+=f'theorem sourceShape : {full}.blocks.toList = original ++ suffix := by\n  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using sourceCoverage\n\n'
    cols=[]
    for r,region in enumerate(artifact['tables']):
        col=f'(UnifiedReduced.Setup.{DATA[region["id"]]}.columns[({column} : Nat)])';cols.append(col)
        pieces=[f'part{i}_{j}' for i,group in enumerate(groups) for j,e in enumerate(group) if e['region']==r]
        text+=f'column_parts_cover regionShape{r} from {col} parts ['+', '.join(pieces)+']\n\n'
        text+=f'theorem regionLength{r} : ({col}.blocks.toList.map Setup.Block.length).sum = {region["length"]} := by decide +kernel\n\n'
    extras=[f'part{i}_{j}' for i,group in enumerate(groups) for j,e in enumerate(group) if e['region'] is None]
    text+='noncomputable def regionBlocks : List Setup.Block := '+' ++ '.join(c+'.blocks.toList' for c in cols)+'\n\n'
    text+='noncomputable def extra : List Setup.Block := '+(' ++ '.join(extras) or '[]')+'\n\n'
    text+='theorem targetShape : regionBlocks ++ extra = targets.flatten := by\n  rw [regionBlocks, '+', '.join(f'regionShape{r}' for r in range(len(cols)))+']\n'
    text+='  simp only [extra, targets, '+', '.join(f'target{i}' for i in range(stop))+', List.flatten_cons, List.flatten_nil, List.append_assoc, List.append_nil]\n\n'
    text+=f'theorem regionTotal : (regionBlocks.map Setup.Block.length).sum = {PREFIX} := by\n  simp only [regionBlocks, List.map_append, List.sum_append, '+', '.join(f'regionLength{r}' for r in range(len(cols)))+']\n\n'
    text+=f'theorem originalLength : (original.map Setup.Block.length).sum = {positions[stop]} := by decide +kernel\n\n'
    text+=f'theorem prefix_value (index : Fin {PREFIX}) : {full}.get? index.val = Setup.getFromBlocks regionBlocks index.val := by\n'
    text+=f'  change Setup.getFromBlocks {full}.blocks.toList index.val = _\n  rw [sourceShape, getFromBlocks_before_suffix original suffix index.val (by rw [originalLength]; have := index.isLt; omega)]\n'
    text+='  rw [sourcesAgree, block_partitions_agree sources targets spansChecked, ← targetShape]\n  exact getFromBlocks_before_suffix regionBlocks extra index.val (by rw [regionTotal]; exact index.isLt)\n\nend '+ns+'\n'
    return f'Airbender.Proofs.GKRProtocol.UnifiedPrefixNative.Column{column}',text


def foundation(column=1):
    name,text=pilot(column,0,0,assemble=True)
    text=text[:text.index('noncomputable def sources')]+f'end Airbender.Compiler.UnifiedPrefixNative.Column{column}\n'
    return f'Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column{column}.Foundation',text


def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--column',type=int,choices=[1],default=1)
    parser.add_argument('--unit',type=int,action='append')
    parser.add_argument('--plan',action='store_true')
    parser.add_argument('--assembly',action='store_true')
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    if args.plan:print_plan();return
    stop=plans(args.column)[3]
    generated=[pilot_assembly(args.column)] if args.assembly else [foundation(args.column)]
    for unit in ([] if args.assembly else args.unit if args.unit is not None else range(8,stop)):
        if not 0<=unit<stop:raise ValueError('source block unit outside actual prefix')
        _,text=pilot(args.column,unit,unit+1,assemble=False)
        generated.append((f'Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column{args.column}.Unit{unit}',text))
    for name,text in generated:
        path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified prefix span scaffold changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(name,flush=True)


if __name__=='__main__':main()
