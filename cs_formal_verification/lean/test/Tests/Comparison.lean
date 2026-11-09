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
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RowContext

@[expose] public section

namespace Tests.Comparison
open Airbender

/-- A selected SLTU row with zero operands and correct lookup results, but an
    unbounded final-PC high limb. This is a local-interface counterexample, not a
    claim that the full decoder/ROM/execution arguments accept the row. -/
def row : Nat → ZMod babyBearModulus
  | 4 | 7 | 13 | 40 | 41 => 1
  | 10 => 3
  | 16 | 18 | 36 => 4
  | 17 => 2013200385
  | _ => 0

theorem unboundedFinalPCSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, row]
  repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
         ((1835008, 0) : fieldPair (ZMod babyBearModulus)) = ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨⟨1835008, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((4, 0, 4) : fieldTriple (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus), ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨4, by decide⟩, rfl⟩)
    | decide

example : ¬ ((⟨4, (row 17).val⟩ : Arithmetic.Word).toBitVec =
    (⟨0, 0⟩ : Arithmetic.Word).toBitVec + 4) := by decide

def edgeRow (signed immediate wrapPC : Bool) : Nat → ZMod babyBearModulus
  | 0 => if wrapPC then 65532 else 0
  | 1 => if wrapPC then 65535 else 0
  | 4 | 5 | 13 | 34 | 37 | 38 => 1
  | 30 | 44 | 47 => if signed then 0 else 1
  | 6 => if immediate then 0 else 2
  | 7 => if immediate then 1 else 2
  | 8 | 9 => if immediate then 65535 else 0
  | 10 => if signed then 2 else 3
  | 16 | 36 => if wrapPC then 0 else 4
  | 18 => 4
  | 39 | 40 => if wrapPC then 1 else 0
  | 26 | 27 => if immediate then 0 else 65535
  | 43 => 65535
  | _ => 0

private def negativeRow : Nat → ZMod babyBearModulus
  | 4 | 5 | 7 | 13 | 30 | 42 | 44 | 47 => 1
  | 6 | 10 => 2
  | 16 | 18 | 36 => 4
  | 22 | 23 | 34 | 35 => 65535
  | _ => 0

end Tests.Comparison
