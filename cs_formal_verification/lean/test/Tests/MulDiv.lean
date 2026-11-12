module
public import Slop.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Slop.MulDiv.Product
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Values
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.RowContext
public import Slop.UnifiedReduced.RV.ControlMembership

@[expose] public section

namespace Tests.MulDiv
open Airbender

-- Dividend 0x20007, divisor zero, PC 0x3fffc. DIVU and REMU route quotient
-- and remainder oppositely; all directed definitions and lookups are checked.
def row (remainder : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 1 => 3
  | 4 | 5 | 7 | 32 | 44 | 55 => 1
  | 6 => 2
  | 12 => if remainder then 0 else 1
  | 13 => if remainder then 1 else 0
  | 15 | 16 => 4
  | 20 | 39 | 45 | 51 | 56 => 7
  | 21 | 40 | 46 | 52 | 57 => 2
  | 28 => if remainder then 7 else 65535
  | 29 => if remainder then 2 else 65535
  | 37 => if remainder then 65535 else 7
  | 38 => if remainder then 65535 else 2
  | 35 | 36 | 60 | 61 => 255
  | 49 | 50 => 65535
  | _ => 0

theorem satisfies (remainder : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row remainder))
      Airbender.MulDiv.importedConstraints := by
  cases remainder <;>
    simp [Airbender.MulDiv.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, row]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (apply Verification.range13_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 131072,
         ((0, 1) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val % 256 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((65535, 255) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val % 256 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨65535, by decide⟩, rfl⟩)
    | decide

example (remainder : Bool) :
    (⟨(row remainder 28).val, (row remainder 29).val⟩ : Arithmetic.Word).toBitVec =
      (if remainder then (⟨7, 2⟩ : Arithmetic.Word).toBitVec else 0xffffffff) := by
  have result := Airbender.MulDiv.Proofs.division_by_zero (by decide) remainder
    (satisfies remainder) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  convert result using 1
  cases remainder <;> decide

example (remainder : Bool) :
    (⟨0, 4⟩ : Arithmetic.Word).toBitVec = (⟨65532, 3⟩ : Arithmetic.Word).toBitVec + 4 := by
  exact (Airbender.MulDiv.Proofs.pc_successor (initial := ⟨65532, 3⟩) (final := ⟨0, 4⟩)
    (by decide) (by decide) (satisfies remainder)
    ⟨rfl, rfl, by change (0 : Nat) = 0; rfl,
      by change (4 : Nat) = (4 : ZMod babyBearModulus).val; decide⟩
    ⟨by decide, by decide⟩).2.2

def falseZeroRow (i : Nat) : ZMod babyBearModulus :=
  if i = 24 then 256 else row false i

/-- A nonzero divisor cannot borrow the exceptional division-by-zero flag. -/
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment falseZeroRow)
    Airbender.MulDiv.importedConstraints := by
  intro h
  have zero := (Airbender.MulDiv.Proofs.divisor_zero_iff (by decide) h).mp rfl
  have notZero : (⟨(falseZeroRow 24).val, (falseZeroRow 25).val⟩ : Arithmetic.Word).value ≠ 0 := by decide
  exact notZero zero

end Tests.MulDiv
