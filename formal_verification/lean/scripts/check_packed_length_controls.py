#!/usr/bin/env python3
"""Require the kernel to reject changed length results and source bindings."""
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PREFIX='''import Tests.PackedLengthChecks
import Airbender.Proofs.Tables.ShiftOutputExtent0
import Lean.AddDecl
open Lean Elab Command
elab "length_proof_control " statement:term " := " proof:term : command => do
  let type ← liftTermElabM do
    let type ← Term.elabType statement
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars type
  let value ← liftTermElabM do
    let value ← Term.elabTerm proof none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  liftCoreM <| addDecl (.thmDecl {name := `LengthControl.result, levelParams := [], type, value})
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
'''


def main():
    owner='Airbender.Verification.ShiftExtentChecks.Lane0.'
    legacy='Airbender.Verification.ShiftCertificate.'
    checker='Airbender.Verification.PackedLengthChecks.check'
    controls=[
        ('numeric counts',f'{checker} Tests.PackedLengthChecks.requests = true',
         f'{checker} [⟨[Code.affine 5 45 2, Code.dense 3 197121, Code.periodic 4 (-1) 3 197121], 21⟩] = true',
         'Tests.PackedLengthChecks.checked'),
        ('complete capture',f'{checker} {owner}requests = true',
         f'{checker} ({owner}requests ++ [⟨[], 1⟩]) = true',owner+'checked'),
        ('complete binding',f'{owner}part0.map (Code.decode 65536) = {legacy}output0Blocks0.toList',
         '([] : List Block) = []',owner+'binding0'),
        ('original extent',f'({legacy}output0Blocks0.toList.map Block.length).sum = 26881',
         f'({legacy}output0Blocks0.toList.map Block.length).sum = 26882',legacy+'output0_extent0'),
    ]
    for label,exact,changed,proof in controls:
        for mutated,statement in [(False,exact),(True,changed)]:
            print('CONTROL',label,'changed' if mutated else 'exact',flush=True)
            with tempfile.TemporaryDirectory(prefix='airbender-length-') as directory:
                path=Path(directory)/'Check.lean';path.write_text(PREFIX+f'length_proof_control ({statement}) := {proof}\n')
                result=subprocess.run(['lean','-j1','-DElab.async=false',str(path)],cwd=ROOT,
                                      stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if not mutated and result.returncode:
                raise SystemExit(f'Exact {label} failed:\n'+result.stdout[-2000:])
            if mutated and (not result.returncode or '(kernel) declaration type mismatch' not in result.stdout.lower()):
                raise SystemExit(f'Changed {label} did not fail in the kernel:\n'+result.stdout[-2000:])
    print('PASS four exact packed length controls; kernel rejects all four mutations')


if __name__=='__main__':main()
