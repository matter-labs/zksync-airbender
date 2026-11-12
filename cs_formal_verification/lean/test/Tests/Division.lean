module
public import Proven.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Proven.MulDiv.Product
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Proven.AddSub.Selectors
public import Proven.JumpBranchSlt.Branch
public import Proven.JumpBranchSlt.Jump
public import Proven.MulDiv.Values
public import Proven.SubwordMemory.Values
public import Proven.Trace.CompositionCore
public import Proven.Trace.RowContext
public import Proven.UnifiedReduced.RV.ControlMembership

@[expose] public section

namespace Tests.Division
open Airbender

-- 13 / 5 = 2, remainder 3. The remainder comparison borrows across its low
-- limb; the PC independently carries from 0x3fffc to 0x40000.
def row (remainder : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 1 => 3
  | 4 | 5 | 7 | 55 => 1
  | 6 | 35 | 49 | 60 => 2
  | 12 => if remainder then 0 else 1
  | 13 => if remainder then 1 else 0
  | 15 | 16 => 4
  | 20 | 45 => 13
  | 24 | 33 | 53 | 58 => 5
  | 28 => if remainder then 3 else 2
  | 37 => if remainder then 2 else 3
  | 39 | 56 => 65534
  | 40 | 57 => 65535
  | 51 => 3
  | _ => 0

private theorem satisfies (remainder : Bool) :
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
         ((5, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨5, by decide⟩, by decide⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((5, 5) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val % 256 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨5, by decide⟩, by decide⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((2, 2) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val % 256 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨2, by decide⟩, by decide⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
         ((0, 0) : fieldPair (ZMod babyBearModulus)) =
           ((i.val : ZMod babyBearModulus), ((i.val % 256 : Nat) : ZMod babyBearModulus))
       exact ⟨⟨0, by decide⟩, rfl⟩)
    | decide

-- The product equality 10 = 1*5 + 5 holds, but remainder = divisor requires
-- comparison high limb 65536, which the imported range lookup rejects.
def badRemainder : Nat → ZMod babyBearModulus
  | 20 | 45 => 10
  | 28 | 51 => 5
  | 35 | 37 | 49 | 60 => 1
  | 39 | 56 => 0
  | 40 | 57 => 65536
  | i => row true i

example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment badRemainder)
    Airbender.MulDiv.importedConstraints := by
  intro h
  have bound := Airbender.MulDiv.Proofs.remainder_lt_divisor (by decide) (by decide)
    h true ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)
  have impossible : ¬ (⟨(badRemainder 51).val, (badRemainder 52).val⟩ : Arithmetic.Word).value <
      (⟨(badRemainder 24).val, (badRemainder 25).val⟩ : Arithmetic.Word).value := by decide
  exact impossible bound

end Tests.Division
