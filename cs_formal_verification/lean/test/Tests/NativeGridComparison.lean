module
import Human.Compiler.NativeSetups.AddSub
import Human.Compiler.NativeSetups.Bigint
import Human.Compiler.NativeSetups.BlakeG
import Human.Compiler.NativeSetups.InitsTeardowns
import Human.Compiler.NativeSetups.JumpBranch
import Human.Compiler.NativeSetups.Keccak
import Human.Compiler.NativeSetups.MulDiv
import Human.Compiler.NativeSetups.ShiftBinop
import Human.Compiler.NativeSetups.SubwordMemory
import Human.Compiler.NativeSetups.Unified
import Human.Compiler.NativeSetups.WordMemory
import Human.Circuits.Blake2Round.SetupArtifact
import Human.Circuits.KeccakSplit.ColumnParity.SetupArtifact
import Human.Circuits.KeccakSplit.ThetaRho.SetupArtifact
import Human.Circuits.KeccakSplit.Chi5.SetupArtifact
meta import Human.Import.NativeGrid

meta section

/- Grid commands must not reserve ordinary proof identifiers. -/
def native_columns : Nat := 0
def native_rows : Nat := 0
def native_model : Nat := 0
open Lean Elab Command Airbender.Import.Setup

run_cmd do
  let constructor ← getConstInfoCtor ``SetupData.mk
  unless constructor.numFields = 4 do
    throwError "The emitted setup contains unused fields."
  let data : SetupData := ⟨4, #[[.dense #[0, 1, 2, 3]]], [], []⟩
  let correct := fun index : Fin 4 => #v[index.val]
  match compareGrid data 0 4 [0] correct with
  | .ok () => pure ()
  | .error reason => throwError "Correct native grid rejected: {reason}"
  match compareGrid data 0 4 [0] (fun index => #v[index.val + 1]) with
  | .error _ => pure ()
  | .ok () => throwError "Wrong grid formula accepted"
  let wrong := { data with columns := #[[.dense #[0, 1, 2, 9]]] }
  match compareGrid wrong 0 4 [0] correct with
  | .error _ => pure ()
  | .ok () => throwError "Wrong native row accepted"
  let ranges : ParsedSetup := {
    traceLen := 524288
    columns := #[]
    range16 := [.affine 65536 0 1, .affine 458752 0 0]
    timestampRange := [.affine 524288 0 1]
    tables := #[] }
  match compareRanges ranges with
  | .ok () => pure ()
  | .error reason => throwError "Correct native ranges rejected: {reason}"
  match compareRanges { ranges with range16 := [.affine 65536 0 1, .affine 458752 1 0] } with
  | .error _ => pure ()
  | .ok () => throwError "Wrong native range padding accepted"
  match compareRanges { ranges with timestampRange := [.affine 524288 1 1] } with
  | .error _ => pure ()
  | .ok () => throwError "Wrong native timestamp prefix accepted"
  let wrongWidth : Array Table := #[⟨4, 0, 4, 2, 2⟩]
  match structureColumn wrongWidth 0 [.affine 4 0 0] with
  | .error _ => pure ()
  | .ok _ => throwError "Wrong native table width accepted"
  let overlapping : Array Table := #[⟨0, 0, 3, 1, 1⟩, ⟨0, 2, 2, 1, 1⟩]
  match structureColumn overlapping 0 [.dense #[0, 1, 2, 3]] with
  | .error _ => pure ()
  | .ok _ => throwError "Overlapping native table regions accepted"

/- Every imported setup is emitted as `SetupData`. -/
run_cmd do
  for name in [
      `Airbender.Compiler.NativeSetups.bigintSetup,
      `Airbender.Compiler.NativeSetups.blakeGSetup,
      `Airbender.Compiler.NativeSetups.keccakSetup,
      `Airbender.Compiler.NativeSetups.mulDivSetup,
      `Airbender.Compiler.NativeSetups.addSubSetup,
      `Airbender.Compiler.NativeSetups.jumpBranchSetup,
      `Airbender.Compiler.NativeSetups.subwordMemorySetup,
      `Airbender.Compiler.NativeSetups.wordMemorySetup,
      `Airbender.Compiler.NativeSetups.shiftBinopSetup,
      `Airbender.Compiler.NativeSetups.initsTeardownsSetup,
      `Airbender.Compiler.NativeSetups.unifiedSetup,
      `Airbender.Blake2Round.blake2RoundSetup,
      `Airbender.Keccak.Split.ColumnParity.columnParitySetup,
      `Airbender.Keccak.Split.ThetaRho.thetaRhoSetup,
      `Airbender.Keccak.Split.Chi5.chi5Setup] do
    let info ← getConstInfoDefn name
    unless info.type.isConstOf ``SetupData do
      throwError "Consumed setup data is absent: {name}"
