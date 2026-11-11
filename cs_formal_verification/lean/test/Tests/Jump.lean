module
public import Slop.Final.Helpers.Context.PCState.Theorems
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Slop.MulDiv.Values
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.RowContext

@[expose] public section

namespace Tests.Jump
open Airbender

def initial (wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨65532, 65535⟩ else ⟨0, 0⟩

def base (indirect wrap : Bool) : Arithmetic.Word :=
  if indirect then (if wrap then ⟨65535, 65535⟩ else ⟨5, 0⟩) else initial wrap

def offset (indirect wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨if indirect then 6 else 8, 0⟩ else ⟨65532, 65535⟩

def final (indirect wrap : Bool) : Arithmetic.Word :=
  if wrap then ⟨4, 0⟩ else if indirect then ⟨0, 0⟩ else ⟨65532, 65535⟩

def row (indirect wrap zero : Bool) : Nat → ZMod babyBearModulus
  | 0 => (initial wrap).lo
  | 1 => (initial wrap).hi
  | 4 => 1
  | 5 => if indirect then 1 else 0
  | 7 => if zero then 0 else 1
  | 8 => (offset indirect wrap).lo
  | 9 => (offset indirect wrap).hi
  | 11 => if indirect then 0 else 1
  | 12 => if indirect then 1 else 0
  | 15 => if zero then 1 else 0
  | 16 => (final indirect wrap).lo
  | 17 => (final indirect wrap).hi
  | 18 => 4
  | 22 => if indirect then (base indirect wrap).lo else 0
  | 23 => if indirect then (base indirect wrap).hi else 0
  | 30 => if zero || wrap then 0 else 4
  | 34 | 47 => if wrap then 0 else 4
  | 36 => if wrap then (if indirect then 5 else 4) else (if indirect then 1 else 65532)
  | 37 | 38 | 41 | 44 => if wrap then 1 else 0
  | 39 | 40 => if indirect || wrap then 1 else 0
  | 42 => if indirect && wrap then 1 else 0
  | _ => 0

def misalignedRow (i : Nat) : ZMod babyBearModulus :=
  if i = 22 then 7 else if i = 36 then 3 else if i = 46 then 1 else row true false false i

/-- Clearing bit 0 of 7+(-4) gives PC 2, rejected by the imported bit-1 check. -/
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment misalignedRow)
    JumpBranchSlt.importedConstraints := by
  intro h
  have target := JumpBranchSlt.Proofs.jump_pc (base := ⟨7, 0⟩) (offset := ⟨65532, 65535⟩)
    (final := ⟨0, 0⟩) (by decide) true h ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (by constructor <;> decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ (by decide) (by decide)
  exact (by decide : ¬ ((⟨0, 0⟩ : Arithmetic.Word).toBitVec =
    ((⟨7, 0⟩ : Arithmetic.Word).toBitVec + (⟨65532, 65535⟩ : Arithmetic.Word).toBitVec) &&& 0xfffffffe)) target.1

end Tests.Jump
