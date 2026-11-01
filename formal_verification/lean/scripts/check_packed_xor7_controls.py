#!/usr/bin/env python3
"""Require exact seven-bit XOR checks and kernel rejection of mutations."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.Blake2G.Xor7PackedCertificate
open Airbender Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
namespace Xor7Control
'''


def main():
    checker='PackedXor7Checks.check';owner='Airbender.Blake2G.Proofs.Xor7PackedCapture.'
    cases=[
        ('payload',f'{checker} 0 [Code.dense 2 65536] = true',f'{checker} 0 [Code.dense 2 65537] = true'),
        ('signed stride',f'{checker} 127 [Code.affine 2 127 (-126)] = true',f'{checker} 127 [Code.affine 2 127 (-127)] = true'),
        ('domain bound',f'{checker} 16383 [Code.affine 1 0 0] = true',f'{checker} 16383 [Code.affine 2 0 0] = true'),
        ('complete native capture',f'{checker} 0 {owner}blocks = true',f'{checker} 0 ({owner}blocks ++ [Code.affine 1 0 0]) = true'),
        ('complete native binding',f'{owner}blocks.map (Code.decode 65536) = (Airbender.Blake2G.xor7Data.columns[2]).blocks.toList',
         f'([] : List Block) = (Airbender.Blake2G.xor7Data.columns[2]).blocks.toList'),
    ]
    for label,exact,changed in cases:
        for mutated,statement in [(False,exact),(True,changed)]:
            with tempfile.TemporaryDirectory(prefix='airbender-xor7-') as directory:
                path=Path(directory)/'Check.lean';path.write_text(PREFIX+f'numeric_data_binding result : {statement}\nend Xor7Control\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print('PASS five exact XOR7 controls; kernel rejects all five mutations')


if __name__=='__main__':main()
