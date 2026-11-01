#!/usr/bin/env python3
"""Require kernel rejection of altered complete fixed Subword requests."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Airbender.Proofs.GKRProtocol.SubwordFixedChecks.Column0
import Airbender.Proofs.GKRProtocol.SubwordFixedChecks.Column1
import Airbender.Proofs.GKRProtocol.SubwordFixedChecks.Column2
import Airbender.Proofs.GKRProtocol.SubwordFixedChecks.Column8
open Airbender Airbender.Compiler
namespace SubwordFixedControl
'''


def main():
    for column in [0,1,2,8]:
        data=f'Airbender.Compiler.SubwordFixedChecks.Column{column}.requests'
        for mutated,requests in [(False,data),(True,f'({data} ++ [⟨[], [], 1⟩])')]:
            with tempfile.TemporaryDirectory(prefix='airbender-subword-fixed-') as directory:
                path=Path(directory)/'Check.lean'
                path.write_text(PREFIX+f'numeric_data_binding result : PackedSetupNormalization.check {requests} = true\nend SubwordFixedControl\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:raise SystemExit(f'Exact column {column} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed column {column} did not fail in the kernel:\n'+result.stdout[-2000:])
    print('PASS four complete fixed Subword controls; kernel rejects all four mutations')


if __name__=='__main__':main()
