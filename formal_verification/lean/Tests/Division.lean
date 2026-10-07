import Airbender.Review.MulDiv.Theorems
import Airbender.Proofs.BabyBear

namespace Tests.Division
open Airbender

-- 13 / 5 = 2, remainder 3. The remainder comparison borrows across its low
-- limb; the PC independently carries from 0x3fffc to 0x40000.
private def row (remainder : Bool) : Nat → ZMod babyBearModulus
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

private def input (remainder : Bool) : Airbender.MulDiv.Input where
  operation := if remainder then .remu else .divu
  left := ⟨13, 0⟩
  right := ⟨5, 0⟩
  pc := ⟨65532, 3⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := .Regidx 1
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (13 : BitVec 32) |>.insert .x2 (5 : BitVec 32)
      |>.insert .PC (262140 : BitVec 32)) }

private def output (remainder : Bool) : Reference.RiscV.Sail.Output :=
  ⟨if remainder then ⟨3, 0⟩ else ⟨2, 0⟩, ⟨0, 4⟩⟩

example (remainder : Bool) : Airbender.MulDiv.spec (input remainder) (output remainder) := by
  apply Airbender.MulDiv.babyBear_soundness (input remainder) (output remainder) (row remainder)
  refine ⟨?_, satisfies remainder, ?_⟩
  · constructor
    all_goals solve
      | (intro i; fin_cases i <;> cases remainder <;>
         dsimp [input, Airbender.MulDiv.Operation.selector, row] <;> decide)
      | (apply Reference.RiscV.Sail.read_register
         cases remainder <;> simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
           Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (constructor <;> cases remainder <;> dsimp [input, row] <;> decide)
  · constructor <;> cases remainder <;> dsimp [input, output, row] <;> decide

-- The product equality 10 = 1*5 + 5 holds, but remainder = divisor requires
-- comparison high limb 65536, which the imported range lookup rejects.
private def badRemainder : Nat → ZMod babyBearModulus
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
