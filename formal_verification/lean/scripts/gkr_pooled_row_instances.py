#!/usr/bin/env python3
"""Compose actual framed compiler rows with public pooled constraints/decoding."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN

CASES = [('AddSub','addSub'),('JumpBranch','jumpBranchSlt'),('MulDiv','mulDiv'),
         ('ShiftBinop','shiftBinop'),('WordMemory','wordMemory'),('SubwordMemory','subwordMemory')]


def module(case, family):
    owner=f'Airbender.Compiler.PooledRowNative.{case}'
    def ns(part): return f'Airbender.Compiler.{part}.{case}'
    full=ns('FullArithmeticNative')+'.native'
    clean=ns('CleanArithmeticNative')+'.native'
    closed=ns('CleanClosedNative')
    helper=ns('HelperValidityNative')+'.native'
    frame=ns('CounterFrameNative')+'.native'
    authored=ns('MaterializedWitnessNative')
    table=ns('TableNative')+'.native'
    decoder=ns('DecoderQueryNative')
    arguments=ns('DecoderArgumentsNative')+'.native'
    model={'addSub':'AddSub','jumpBranchSlt':'JumpBranchSlt','mulDiv':'MulDiv',
           'shiftBinop':'ShiftBinop','wordMemory':'WordMemory','subwordMemory':'SubwordMemory'}[family]
    text=f'''import GKRProtocol.CleanClosedNative.{case}
import GKRProtocol.DecoderQueryNative.{case}
import GKRProtocol.FramedWitnessNative.{case}
import GKRProtocol.PublicConstraints
import GKRProtocol.ROMNative.WordFullPublic
import GKRProtocol.ROMNative.SubwordPublic
import Airbender.Review.Helpers.Decoder.PooledProgram

namespace {owner}
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The same canonical source frame and actual native arithmetic relation used
by the complete compiler-witness theorem. Logical lookup validity is explicit. -/
structure Certificate where
  sourceValue : Fin {full}.inputs.length → Source.BaseField
  counts : Fin {table}.multiplicityColumns.length → Source.BaseField
  physical : GKRAddress → Source.BaseField
  frame : ∀ wire, physical ({full}.inputBank.address wire) =
    {frame}.assigned ({helper}.canonical sourceValue) counts wire
  arithmetic : ∀ gate ∈ {full}.artifact.gates,
    gate.expressionResidual (physical ∘ {full}.bank.address) = 0
  helpers : ∀ field ∈ {ns('HelperNative')}.native.fields,
    (field.value ({ns('HelperNative')}.native.sourceValues physical)).val < 524288
  authored : {authored}.AuthoredLookupValid sourceValue
  active : ({clean}.environment physical (fun _ _ => #[])).get
    Airbender.{model}.importedConstraintsTraceColumns.execute = 1

/-- A complete native graph witness supplies the arithmetic, canonical frame
and helper range fields of the execution cert without additional claims. -/
def ofWitness {{R : Type}} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (sourceValue : Fin {full}.inputs.length → Source.BaseField)
    (counts : Fin {table}.multiplicityColumns.length → Source.BaseField)
    (index : Fin {ns('MaterializedNative')}.native.model.imported.data.length)
    (fallback physical : GKRAddress → Source.BaseField) (values : GKRAddress → R)
    (native : {ns('FramedWitnessNative')}.CompleteRowWitness hom challenges gamma sourceValue counts index fallback physical values)
    (authored : {authored}.AuthoredLookupValid sourceValue)
    (active : ({clean}.environment physical (fun _ _ => #[])).get
      Airbender.{model}.importedConstraintsTraceColumns.execute = 1) : Certificate := by
  rcases native.1 with ⟨inputsAt, arithmetic, _, _, _, _, _, _, helpers, _⟩
  exact ⟨sourceValue, counts, physical, inputsAt, arithmetic, helpers, authored, active⟩

def row (cert : Certificate) : Trace.Row babyBearModulus Trace.PooledFamily :=
  ⟨.{family}, ({clean}.environment cert.physical (fun _ _ => #[])).get⟩

theorem active (cert : Certificate) :
    (row cert).assignment (row cert).columns.execute = 1 := cert.active

theorem constraints (cert : Certificate) {{before : Reference.RiscV.Sail.State}}
    (image : Trace.ROM.ImportedImage before) {{cells : List Trace.Cell}}
    {{tokens : List (Trace.MemoryToken babyBearModulus)}}
    (physical : Trace.initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row cert).assignment)
      ((row cert).constraints (⟨Trace.ROM.table cells tokens,
        Verification.subwordTable (Trace.ROM.words before)⟩ : Trace.PooledSetup babyBearModulus)) := by
  have native := {closed}.retained_clock_from_source cert.sourceValue cert.counts
    cert.physical (fun _ _ => #[]) cert.frame cert.arithmetic cert.helpers cert.authored
'''
    if family=='wordMemory':
        text+='''  exact PublicConstraints.word_transport _ _ _ native
    (fun _ member guard => ROMNative.WordFullPublic.public_refinement image physical domain member guard)
'''
    elif family=='subwordMemory':
        text+='''  exact PublicConstraints.subword_transport _ _ _ native
    (fun _ member guard => ROMNative.SubwordPublic.public_table_refinement image member guard)
'''
    else:
        text+='  exact native\n'
        # These public inputs are intentionally unused for fixed-table families.
        text=text.replace('set_option warningAsError true','set_option warningAsError true\nset_option linter.unusedVariables false')
    text+=f'''
theorem decoded (cert : Certificate)
    (typed : (row cert).decoderQuery[0].val < 65536) :
    (Trace.decoderTable Trace.NativeDecoder.pooledProgram (row cert).family).Contains #[]
      (row cert).decoderQuery := by
  apply {decoder}.program_from_framed_source (by decide +kernel)
    cert.sourceValue cert.counts cert.physical (fun _ _ => #[])
    cert.frame cert.arithmetic typed ?_ cert.authored
  have enabled := cert.active
  simpa [{arguments}.expression0, _root_.Expression.eval] using
    (show (({clean}.environment cert.physical (fun _ _ => #[])).get
      Airbender.{model}.importedConstraintsTraceColumns.execute) ≠ 0 by rw [enabled]; exact one_ne_zero)

end {owner}
'''
    if family=='subwordMemory':
        text=text.replace('(physical : Trace.initialImage', '(_physical : Trace.initialImage').replace('(domain : ROMNative.WordFullPublic.CoversROM', '(_domain : ROMNative.WordFullPublic.CoversROM')
    return 'GKRProtocol.PooledRowNative.'+case,text


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    parser.add_argument('--case')
    args=parser.parse_args()
    for stem,family in CASES:
        for mode in ['Uncached','Cached']:
            case=stem+mode
            if args.case and case!=args.case:continue
            name,text=module(case,family);path=LEAN/(name.replace('.','/')+'.lean')
            if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('pooled compiler row changed: '+name)
            if args.write and (not path.exists() or path.read_text()!=text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
            print(name,flush=True)
            if args.build:subprocess.run(['lake','--no-cache','build','+'+name+':olean'],cwd=LEAN,
                env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)

if __name__=='__main__':main()
