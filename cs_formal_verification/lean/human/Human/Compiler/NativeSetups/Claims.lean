module
public import Human.Compiler.NativeFixedRows
public import Human.Compiler.NativeSetups.AddSub
public import Human.Compiler.NativeSetups.JumpBranch
public import Human.Compiler.NativeSetups.MulDiv
public import Human.Compiler.NativeSetups.ShiftBinop
public import Human.Compiler.NativeSetups.WordMemory
public import Human.Compiler.NativeSetups.SubwordMemory
public import Human.Compiler.NativeSetups.Unified

@[expose] public section
namespace Airbender.Compiler.NativeFixedRows
open Airbender Trace Arithmetic Verification

/- Import claims of the CPU fixed regions: each table definition, with the setup fixture program, equals the imported
   native rows on the complete trace domain. This module reads the raw setup data; the definitions that the machine
   claims use (`NativeFixedRows`, `NativePublicSetup`) do not import it. -/

/-- Decoder slot `slot` of the add/sub setup for the setup fixture program. The fields are the PC limbs, `rs1`,
    `rs2`, `rd`, the immediate limbs and the mask. Slot 0 holds `addi x0, x0, 0`, slot 1 `addi x1, x1, 4` and slot 3
    `add x3, x3, x7`; every other slot holds the field element `-1` in each field. -/
def addSubFixtureDecoderRow (slot : Nat) : Vector Int 8 :=
  if slot = 0 then #v[0, 0, 0, 0, 0, 0, 0, 1]
  else if slot = 1 then #v[4, 0, 1, 0, 1, 4, 0, 1]
  else if slot = 3 then #v[12, 0, 3, 7, 3, 0, 0, 1]
  else Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)

/-- The add/sub setup has no fixed region: the decoder rows of the setup fixture program, then rows that hold the
    field element `-1` in each field, are the imported native rows on the complete trace domain. -/
def AddSubImportClaim : Prop :=
  NativeSetups.addSubSetup.traceLen = 16777216 ∧
  NativeSetups.addSubSetup.Rows fun index =>
    if index < 1048576 then addSubFixtureDecoderRow index
    else Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)

/-- Decoder slot `slot` of the jump/branch setup for the setup fixture program: slot 2 (PC 8) holds `jal x0, 0` (PC
    limbs 8 and 0, zero registers and immediate, mask 17), every other slot the field element `-1` in each payload
    field; the tag is 46. -/
def jumpBranchFixtureDecoderRow (slot : Nat) : Vector Int 10 :=
  if slot = 2 then #v[8, 0, 0, 0, 0, 0, 0, 0, 17, 46]
  else (Vector.replicate 9 ((babyBearModulus - 1 : Nat) : Int)).push 46

/-- The jump/branch fixed rows, the decoder rows of the setup fixture program, then zero padding, are the imported
    native rows on the complete trace domain. -/
def JumpBranchImportClaim : Prop :=
  NativeSetups.jumpBranchSetup.traceLen = 16777216 ∧
  NativeSetups.jumpBranchSetup.Rows fun index =>
    if bound : index < 4456448 then (jumpBranch ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 5505024 then jumpBranchFixtureDecoderRow (index - 4456448)
    else Vector.replicate 10 0

/-- The multiply/divide fixed rows, the decoder rows of the setup fixture program, then zero padding, are the imported
    native rows on the complete trace domain. The fixture program has no multiply or divide instruction: each decoder
    row holds the field element `-1` in every payload field and the tag 46. -/
def MulDivImportClaim : Prop :=
  NativeSetups.mulDivSetup.traceLen = 8388608 ∧
  NativeSetups.mulDivSetup.Rows fun index =>
    if bound : index < 270336 then (mulDiv ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 1318912 then (Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)).push 46
    else Vector.replicate 9 0

/-- The word-ROM rows of the setup fixture program, its decoder rows, then zero padding, are the imported native rows
    on the complete trace domain. The fixture program has no word load or store: each decoder row holds the field
    element `-1` in every payload field and the tag 46. -/
def WordMemoryImportClaim : Prop :=
  NativeSetups.wordMemorySetup.traceLen = 16777216 ∧
  NativeSetups.wordMemorySetup.Rows fun index =>
    if bound : index < 1048577 then
      (wordMemory NativeSetups.fixtureWords ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 2097153 then (Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)).push 46
    else Vector.replicate 9 0

/-- The subword fixed rows and the ROM rows of the setup fixture program, its decoder rows, then zero padding, are the
    imported native rows on the complete trace domain. The fixture program has no subword load or store: each decoder
    row holds the field element `-1` in every payload field and the tag 46. -/
def SubwordMemoryImportClaim : Prop :=
  NativeSetups.subwordMemorySetup.traceLen = 16777216 ∧
  NativeSetups.subwordMemorySetup.Rows fun index =>
    if bound : index < 13238273 then
      (subwordRow NativeSetups.fixtureWords ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 14286849 then (Vector.replicate 8 ((babyBearModulus - 1 : Nat) : Int)).push 46
    else Vector.replicate 9 0

/-- Decoder slot `slot` of the unified setup for the setup fixture program. The fields are the PC limbs, `rs1`, `rs2`,
    `rd`, the immediate limbs, a zero field, the mask and the tag 46. Slot 0 holds `addi x0, x0, 0`, slot 1
    `addi x1, x1, 4`, slot 2 `jal x0, 0` and slot 3 `add x3, x3, x7`; every other slot holds the field element `-1` in
    each payload field. -/
def unifiedFixtureDecoderRow (slot : Nat) : Vector Int 10 :=
  if slot = 0 then #v[0, 0, 0, 0, 0, 0, 0, 0, 1, 46]
  else if slot = 1 then #v[4, 0, 1, 0, 1, 4, 0, 0, 1, 46]
  else if slot = 2 then #v[8, 0, 0, 0, 0, 0, 0, 0, 17408, 46]
  else if slot = 3 then #v[12, 0, 3, 7, 3, 0, 0, 0, 1, 46]
  else (Vector.replicate 9 ((babyBearModulus - 1 : Nat) : Int)).push 46

/-- The unified fixed rows in native row order (`unified`, which `NativePublicSetup.fixedRow` reads) with the ROM rows
    of the setup fixture program, its decoder rows, then zero padding, are the imported native rows on the complete
    trace domain. -/
def UnifiedImportClaim : Prop :=
  NativeSetups.unifiedSetup.traceLen = 8388608 ∧
  NativeSetups.unifiedSetup.Rows fun index =>
    if bound : index < 2097537 then (unified NativeSetups.fixtureWords ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 3146113 then unifiedFixtureDecoderRow (index - 2097537)
    else Vector.replicate 10 0

end Airbender.Compiler.NativeFixedRows

namespace Airbender.Verification

/-- The fixed rows, the decoder rows of the setup fixture program, then zero padding, are the imported native rows on
    the complete trace domain. The fixture program has no shift or binary instruction: each decoder row holds the
    field element `-1` in every payload field and the tag 46. -/
def ShiftBinopImportClaim : Prop :=
  Compiler.NativeSetups.shiftBinopSetup.traceLen = 16777216 ∧
  Compiler.NativeSetups.shiftBinopSetup.Rows fun index =>
    if bound : index < 524545 then (shiftBinopRow ⟨index, bound⟩).map (fun n : Nat => (n : Int))
    else if index < 1573121 then (Vector.replicate 9 ((babyBearModulus - 1 : Nat) : Int)).push 46
    else Vector.replicate 10 0

end Airbender.Verification
