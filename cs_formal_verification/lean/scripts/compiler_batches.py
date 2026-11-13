#!/usr/bin/env python3
"""Export checked compiler declarations and split their explicit source into small modules."""
from pathlib import Path
import argparse
import json
import re
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("action", choices=("export", "split"))
parser.add_argument("names", nargs="*")
args = parser.parse_args()
entries = json.loads((root / "gen/compiler/manifest.json").read_text())["entries"]
selected = set(args.names) if args.names else {entry["name"] for entry in entries}
unknown = selected - {entry["name"] for entry in entries}
if unknown:
    parser.error("Unknown compiler source: " + ", ".join(sorted(unknown)))
export_dir = root / ".lake/compiler-exports"
export_dir.mkdir(parents=True, exist_ok=True)
manifest = []
for entry in entries:
    if entry["name"] not in selected:
        continue
    wrapper = export_dir / (entry["name"] + ".lean")
    destination = root / entry["output"]
    if args.action == "export":
        destination.write_text("")
        text = (root / entry["source"]).read_text()
        text = text.replace("@[expose] public section", f'@[expose] public section\nset_option fv.compilerExport "{destination}"', 1)
        wrapper.write_text(text)
        log = export_dir / (entry["name"] + ".log")
        with log.open("w") as output:
            subprocess.run(["lake", "env", "lean", str(wrapper)], cwd=root, stdout=output, stderr=subprocess.STDOUT, check=True)
        print("Exported", entry["name"])
    manifest.append((entry["name"], str(wrapper), str(destination), entry["relative"]))
if args.action == "export":
    raise SystemExit(0)

def list_items(value):
    result=[];level=0;begin=1
    for index,char in enumerate(value[1:-1],1):
        if char in '([{⟨':level+=1
        elif char in ')]}⟩':level-=1
        elif char==',' and level==0:result.append(value[begin:index].strip());begin=index+1
    final=value[begin:-1].strip()
    if final:result.append(final)
    return result

def split_literal(block):
    match=re.match(r'((?:noncomputable )?def) ([A-Za-z_][A-Za-z0-9_.]*)\s*:\s*(List\b.*?)\s*:=\s*(.*)',block,re.S)
    if not match or len(block)<24000:return [block]
    modifier,name,type_,value=match.groups();value=value.strip()
    if not(value.startswith('[') and value.endswith(']')):return [block]
    items=list_items(value)
    if len(items)<2:return [block]
    groups=[];current=[];size=0
    for item in items:
        if current and size+len(item)>12000:groups.append(current);current=[];size=0
        current.append(item);size+=len(item)
    if current:groups.append(current)
    parts=[f'{name}.part{index:03d}' for index in range(len(groups))]
    declarations=[f'{modifier} {part} : {type_} := ['+',\n'.join(group)+']' for part,group in zip(parts,groups)]
    declarations.append(f'{modifier} {name} : {type_} := '+' ++ '.join(parts))
    return declarations

for stem,wrapper,destination,relative in manifest:
    if stem not in selected:continue
    exported=Path(destination).read_text()
    if not exported.strip():raise SystemExit('Missing export '+stem)
    original=root/'proven/Proven/GKRProtocol'/relative
    source=Path(wrapper).read_text()
    source=re.sub(r'^set_option fv.compilerExport .*\n','',source,flags=re.M)
    first=re.search(r'^(?:import_full_compiler_arithmetic|import_clean_arithmetic|numeric_polynomials|packed_normalization_rows)\b',source,re.M)
    if not first:raise SystemExit('Missing source command '+stem)
    header=source[:first.start()];footer=source[source.rfind('\nend '):]
    header=header.replace('module\n','module\npublic import Proven.KernelRfl\n',1)
    owner=re.findall(r'^namespace (\S+)',header,re.M)[-1]
    blocks=[part.strip().replace('✝','') for part in exported.split('-- COMPILER_DECL_END') if part.strip()]
    theoremNames={match.group(1) for block in blocks if (match:=re.match(r'theorem ([A-Za-z_][A-Za-z0-9_.]*)',block))}
    retained=[]
    for block in blocks:
        outer=re.match(r'numeric_data_binding ([A-Za-z_][A-Za-z0-9_.]*)',block)
        if outer:
            if outer.group(1) not in theoremNames:raise SystemExit('Missing checked expansion '+outer.group(1))
        else:retained.append(block)
    blocks=[re.sub(r':=\s*by\s+rfl\b', ':= by kernel_rfl', block) for block in retained]
    # Manual declarations in a source file are checked by the export run too.
    body=source[first.start():source.rfind('\nend ')]
    commands=list(re.finditer(r'^(?:(?:noncomputable )?(?:def|theorem) |numeric_[A-Za-z_]+ |packed_normalization_rows |import_[A-Za-z_]+ )',body,re.M))
    for position,command in enumerate(commands):
        if re.match(r'(?:(?:noncomputable )?def|theorem) ',body[command.start():]):
            end=commands[position+1].start() if position+1<len(commands) else len(body)
            blocks.append(body[command.start():end].strip())
    instances=[block for block in blocks if block.startswith('local instance')]
    blocks=[block for block in blocks if not block.startswith('local instance')]
    declarations=[]
    for block in blocks:declarations.extend(split_literal(block))
    # Resolve actual declaration dependencies before grouping the output.
    symbolPattern=re.compile(r'(?:noncomputable )?(?:def|theorem) ([A-Za-z_][A-Za-z0-9_.]*)')
    symbols={symbolPattern.match(block).group(1):index for index,block in enumerate(declarations)}
    tokenPattern=re.compile(r'\b[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*')
    ordering=[];visited=set();visiting=set()
    def visit(index):
        if index in visited:return
        if index in visiting:raise SystemExit('Cyclic generated declaration')
        visiting.add(index)
        for identifier in tokenPattern.findall(declarations[index]):
            if identifier.startswith(owner+'.'):identifier=identifier[len(owner)+1:]
            while identifier:
                if identifier in symbols:
                    dependency=symbols[identifier]
                    if dependency!=index:visit(dependency)
                    break
                identifier=identifier.rsplit('.',1)[0] if '.' in identifier else ''
        visiting.remove(index);visited.add(index);ordering.append(index)
    for index in range(len(declarations)):visit(index)
    declarations=[declarations[index] for index in ordering]
    groups=[];current=[];size=0
    for block in declarations:
        if current and (size+len(block)>38000 or len(current)>=24):groups.append(current);current=[];size=0
        current.append(block);size+=len(block)
    if current:groups.append(current)
    module='Proven.GKRProtocol.'+relative.removesuffix('.lean').replace('/','.')
    parent=original.with_suffix('');parent.mkdir(exist_ok=True)
    for stale in parent.glob('Part[0-9]*.lean'):stale.unlink()
    names={}
    for index,group in enumerate(groups):
        for block in group:
            found=re.match(r'(?:noncomputable )?(?:def|theorem) ([A-Za-z_][A-Za-z0-9_.]*)',block)
            if not found:raise SystemExit('Unknown generated declaration '+block[:100])
            name=found.group(1)
            if name in names:raise SystemExit('Duplicate declaration '+name)
            names[name]=index
    token=re.compile(r'\b[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*')
    for index,group in enumerate(groups):
        deps=set()
        for identifier in token.findall('\n'.join(group)):
            if identifier.startswith(owner+'.'):identifier=identifier[len(owner)+1:]
            while identifier:
                if identifier in names:
                    earlier=names[identifier]
                    if earlier<index:deps.add(earlier)
                    break
                identifier=identifier.rsplit('.',1)[0] if '.' in identifier else ''
        imports=''.join(f'public import {module}.Part{dependency:03d}\n' for dependency in sorted(deps))
        content=header.replace('module\n','module\n'+imports,1)
        for instanceIndex,instance in enumerate(instances):
            content+=instance.replace('local instance :',f'local instance generatedBatch{index}Instance{instanceIndex} :',1)+'\n\n'
        content+='\n\n'.join(group)+footer
        parent.joinpath(f'Part{index:03d}.lean').write_text(content)
    original.write_text('module\n'+''.join(f'public import {module}.Part{index:03d}\n' for index in range(len(groups))))
    print(stem,len(blocks),'original declarations ->',len(declarations),'factored declarations in',len(groups),'explicit modules')
