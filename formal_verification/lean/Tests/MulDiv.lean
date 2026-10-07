import Airbender.Review.MulDiv.Theorems
import Airbender.Proofs.BabyBear

namespace Tests.MulDiv
open Airbender

-- Dividend 0x20007, divisor zero, PC 0x3fffc. DIVU and REMU route quotient
-- and remainder oppositely; all directed definitions and lookups are checked.
private def row (remainder : Bool) : Nat → ZMod babyBearModulus
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
  have result := Airbender.MulDiv.division_by_zero (by decide) remainder
    (satisfies remainder) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  convert result using 1
  cases remainder <;> decide

example (remainder : Bool) :
    (⟨0, 4⟩ : Arithmetic.Word).toBitVec = (⟨65532, 3⟩ : Arithmetic.Word).toBitVec + 4 := by
  exact (Airbender.MulDiv.pc_successor (initial := ⟨65532, 3⟩) (final := ⟨0, 4⟩)
    (by decide) (by decide) (satisfies remainder)
    ⟨rfl, rfl, by change (0 : Nat) = 0; rfl,
      by change (4 : Nat) = (4 : ZMod babyBearModulus).val; decide⟩
    ⟨by decide, by decide⟩).2.2

private def falseZeroRow (i : Nat) : ZMod babyBearModulus :=
  if i = 24 then 256 else row false i

/-- A nonzero divisor cannot borrow the exceptional division-by-zero flag. -/
example : ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment falseZeroRow)
    Airbender.MulDiv.importedConstraints := by
  intro h
  have zero := (Airbender.MulDiv.divisor_zero_iff (by decide) h).mp rfl
  have notZero : (⟨(falseZeroRow 24).val, (falseZeroRow 25).val⟩ : Arithmetic.Word).value ≠ 0 := by decide
  exact notZero zero

private def input (remainder : Bool) : Airbender.MulDiv.Input where
  operation := if remainder then .remu else .divu
  left := ⟨7, 2⟩
  right := ⟨0, 0⟩
  pc := ⟨65532, 3⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 2
  rd := .Regidx 1
  before := { (default : Reference.RiscV.Sail.State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (131079 : BitVec 32) |>.insert .x2 (0 : BitVec 32)
      |>.insert .PC (262140 : BitVec 32)) }

private def output (remainder : Bool) : Reference.RiscV.Sail.Output :=
  ⟨if remainder then ⟨7, 2⟩ else ⟨65535, 65535⟩, ⟨0, 4⟩⟩

/-- Both actual Sail clauses, source/destination aliasing and native PC carry. -/
example (remainder : Bool) :
    Airbender.MulDiv.spec (input remainder) (output remainder) := by
  apply Airbender.MulDiv.babyBear_soundness
    (input remainder) (output remainder) (row remainder)
  refine ⟨?_, satisfies remainder, ?_⟩
  · constructor
    all_goals solve
      | (intro i; fin_cases i <;> cases remainder <;>
         dsimp [input, Airbender.MulDiv.Operation.selector, row] <;> decide)
      | (apply Reference.RiscV.Sail.read_register
         cases remainder <;> simp [input, Arithmetic.Word.toBitVec, Arithmetic.Word.value,
           Arithmetic.limbBase, Std.ExtDHashMap.get?_insert])
      | (change (⟨7, 2⟩ : Arithmetic.Word).Bounded; exact ⟨by decide, by decide⟩)
      | (change (⟨65532, 3⟩ : Arithmetic.Word).Bounded; exact ⟨by decide, by decide⟩)
  · constructor <;> cases remainder <;> dsimp [input, output, row] <;> decide

end Tests.MulDiv
