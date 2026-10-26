#!/usr/bin/env python3
"""Bind retained logical decoder fields to actual source/native operands."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import FAMILIES,LEAN
from gkr_wiring_instances import CASES
from gkr_clean_links import MODELS
from gkr_lookup_source_certificate import synthesis


def module(family,case,model,mode):
    name=family+'-'+mode
    pair=json.loads((LEAN/'artifacts/compiler'/f'{name}.json').read_text())
    if not pair['source']['remaining_inputs']['executor']:return None
    target='Airbender.Proofs.GKRProtocol.DecoderArgumentsNative.'+case
    namespace='Airbender.Compiler.DecoderArgumentsNative.'+case
    certificate=json.loads((LEAN/'artifacts/compiler/lookup'/f'{name}.json').read_text())
    decoders=[operand for operand in synthesis(pair,certificate)['operands'] if operand['kind']=='decoder']
    if len(decoders)!=1:raise ValueError('decoder query inventory changed: '+case)
    query=decoders[0]['native_leaf']
    text=('import Airbender.Import.GKRProtocol.DecoderArgumentsImport\n'
        f'import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.{case}\n'
        f'import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.{case}\n'
        f'import Airbender.Proofs.GKRProtocol.LookupSourceNative.{case}\n'
        f'import Airbender.Review.Circuits.{model}.Artifact\n\n'
        f'namespace {namespace}\nopen Airbender Airbender.Compiler\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n\n'
        f'import_decoder_arguments native from "artifacts/compiler/{name}.json"\n'
        f'  certificate "artifacts/compiler/lookup/{name}.json"\n')
    for key,kind in [('clean_model','CleanArithmeticNative'),('base_model','FullArithmeticNative'),
                     ('lookup_model','LookupNative'),('query_model','LookupSourceNative'),
                     ('links_model','FunctionalLinksNative')]:
        text+=f'  {key} Airbender.Compiler.{kind}.{case}.native\n'
    text+=f'  source_query Airbender.Compiler.LookupSourceNative.{case}.native.query{query}\n'
    text+=f'  trace_columns Airbender.{model}.importedConstraintsTraceColumns\n'
    text+=f'  decoder_columns Airbender.{model}.importedConstraintsDecoderColumns\n\nend {namespace}\n'
    return target,text


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family',choices=FAMILIES,action='append')
    parser.add_argument('--mode',choices=['uncached','cached'],action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();count=0
    for family,stem,model in zip(FAMILIES,CASES,MODELS,strict=True):
        if args.family and family not in args.family:continue
        for mode in args.mode or ['uncached','cached']:
            generated=module(family,stem+mode.title(),model,mode)
            if generated is None:continue
            target,text=generated;path=LEAN/(target.replace('.','/')+'.lean');count+=1
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('decoder argument scaffold changed: '+target)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(target,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)
    if args.family is None and args.mode is None and count!=14:raise ValueError('executor decoder inventory changed')

if __name__=='__main__':main()
