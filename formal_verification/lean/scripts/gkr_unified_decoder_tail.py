#!/usr/bin/env python3
"""Reuse checked native prefixes to bind the complete decoder/padding tail."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN


def module(column):
    parent=f'UnifiedPrefixNative.Column{column}' if column==1 else f'UnifiedAllPrefix.Column{column}'
    original='original' if column==1 else 'originals.flatten'
    owner=f'Airbender.Compiler.DecoderTail.Unified.Column{column}'
    text=(f'import Airbender.Proofs.GKRProtocol.DecoderTailNormalization\nimport Airbender.Proofs.GKRProtocol.{parent}\n'
        'import Airbender.Data.Decoder.Setup.Unified\n\n'
        f'namespace {owner}\nopen Airbender Airbender.Compiler Airbender.Compiler.{parent}\n'
        'set_option warningAsError true\nset_option Elab.async false\n'
        'set_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
        'theorem tail_value (index : Nat) :\n'
        f'    Data.GKRSetup.Unified.setupColumn{column}.get? (2097537 + index) =\n'
        '      Setup.getFromBlocks (extra ++ suffix) index := by\n'
        f'  apply column_tail_value _ {original} regionBlocks extra suffix 2097537 sourceShape\n'
        '  · rw [originalLength, List.map_append, List.sum_append, regionTotal]\n'
        '    decide +kernel\n  · intro position\n')
    if column==1:
        text+='    exact ((congrArg (fun blocks => Setup.getFromBlocks blocks position) sourcesAgree).trans\n      (block_partitions_agree sources targets spansChecked position)).trans\n'
    else:text+='    exact (block_chunks_agree originals targets chunksChecked position).trans\n'
    text+='      (congrArg (fun blocks => Setup.getFromBlocks blocks position) targetShape).symm\n  · exact regionTotal\n\n'
    text+=f'noncomputable def targetTail : List Setup.Block :=\n  Trace.NativeDecoder.unifiedSetup.realRows.columns[{column}].blocks.toList ++\n  Trace.NativeDecoder.unifiedSetup.padding.columns[{column}].blocks.toList\n\n'
    text+='theorem tail_checked : normalizeDecoderTail (extra ++ suffix) = normalizeDecoderTail targetTail := by\n  rfl\n\n'
    text+=f'theorem decoder_tail_value (index : Nat) :\n    Data.GKRSetup.Unified.setupColumn{column}.get? (2097537 + index) = Setup.getFromBlocks targetTail index :=\n'
    text+='  (tail_value index).trans ((normalize_decoder_tail_sound (extra ++ suffix) index).symm.trans\n    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans\n      (normalize_decoder_tail_sound targetTail index)))\n\nend '+owner+'\n'
    return f'Airbender.Proofs.GKRProtocol.DecoderTail.Unified.Column{column}',text


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--column',type=int,choices=range(10),action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for column in args.column or range(10):
        name,text=module(column);path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified decoder tail scaffold changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
        print(name,flush=True)
        if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
