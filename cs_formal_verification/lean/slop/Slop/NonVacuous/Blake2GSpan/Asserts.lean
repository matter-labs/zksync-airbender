module
public import Slop.NonVacuous.Blake2GSpan.Honest
public import Slop.NonVacuous.ClockCompleteness
public import Slop.Blake2G.OpIndex
public import Slop.Blake2G.ArtifactChecks
public import Mathlib.Tactic.LinearCombination
public import Slop.NonVacuous.SpanTactics

@[expose] public section

/-! The 32 imported assertions of a G row hold for the honest assignment of valid inputs: the active flag, the zero
    high limbs of x12, the four addition equations and four rotated-word equations, and the twelve carry and nine
    borrow flags. Each cast_identity is the cast of a natural-number identity of the honest values (`omega`). -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic

variable {p : Nat} [Fact p.Prime]

theorem asserts (x : RowInput) (valid : x.Valid) (setup : Table (ZMod p) (fields 9)) :
    ∀ i (h : i < (FlatOperation.constraints (Blake2G.importedConstraints setup)).length),
      ((FlatOperation.constraints (Blake2G.importedConstraints setup)).get ⟨i, h⟩).eval
        (Verification.environment x.assignment) = 0 := by
  have a := valid.a
  have b := valid.b
  have c := valid.c
  have d := valid.d
  have mx := valid.mx
  have my := valid.my
  simp only [Word.Bounded, limbBase] at a b c d mx my
  obtain ⟨xd0, xd1, xd2, xd3, xb0, xb1, xb2, xb3, xb4, xb5, xe0, xe1, xe2, xe3, -, -, -, -⟩ := valid.xors
  intro i h
  have size : i < 32 := by rwa [Blake2G.constraint_count] at h
  have bit {k n : Nat} (column : x.assignment (p := p) k = (n : ZMod p)) (bound : n ≤ 1) :=
    flag_eval column bound
  interval_cases i <;> op_index
  · simp only [Expression.eval, Verification.environment, honest_column]
    push_cast
    ring
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · cast_identity p (show x.a.lo + x.b.lo + x.mx.lo + x.xb2 + 16 * x.xb3 + 128 * x.xb4 + x.my.lo =
      65536 * (x.carryA0 % 2) + 131072 * (x.carryA0 / 2) + 65536 * (x.carryA2 % 2) + 131072 * (x.carryA2 / 2) +
        x.a2lo by
      simp only [RowInput.carryA0, RowInput.carryA2, RowInput.a2lo, RowInput.sumA2, RowInput.b1lo, RowInput.sumA0,
        RowInput.a1lo]
      omega)
  · cast_identity p (show x.a.hi + x.b.hi + x.mx.hi + x.carryA0 % 2 + 2 * (x.carryA0 / 2) + x.xb5 + 16 * x.xb0 +
      128 * x.xb1 + x.my.hi + x.carryA2 % 2 + 2 * (x.carryA2 / 2) =
      65536 * (x.carryA1 % 2) + 131072 * (x.carryA1 / 2) + 65536 * (x.carryA3 % 2) + 131072 * (x.carryA3 / 2) +
        x.a2hi by
      simp only [RowInput.carryA1, RowInput.carryA3, RowInput.a2hi, RowInput.sumA3, RowInput.b1hi, RowInput.sumA1,
        RowInput.a1hi]
      omega)
  · cast_identity p (show x.xf1 + 512 * x.xf2 = x.b2lo from rfl)
  · cast_identity p (show x.xf3 + 512 * x.xf0 = x.b2hi from rfl)
  · cast_identity p (show x.c.lo + x.xd2 + 256 * x.xd3 + x.xe1 + 256 * x.xe2 =
      65536 * x.carryC0 + 65536 * x.carryC2 + x.c2lo by
      simp only [RowInput.carryC0, RowInput.carryC2, RowInput.c2lo, RowInput.sumC2, RowInput.d2lo, RowInput.sumC0,
        RowInput.c1lo, RowInput.d1lo]
      omega)
  · cast_identity p (show x.c.hi + x.xd0 + 256 * x.xd1 + x.carryC0 + x.xe3 + 256 * x.xe0 + x.carryC2 =
      65536 * x.carryC1 + 65536 * x.carryC3 + x.c2hi by
      simp only [RowInput.carryC1, RowInput.carryC3, RowInput.c2hi, RowInput.sumC3, RowInput.d2hi, RowInput.sumC1,
        RowInput.c1hi, RowInput.d1hi]
      omega)
  · cast_identity p (show x.xe1 + 256 * x.xe2 = x.d2lo from rfl)
  · cast_identity p (show x.xe3 + 256 * x.xe0 = x.d2hi from rfl)
  · exact bit (RowInput.assignment_37 x) (by omega)
  · exact bit (RowInput.assignment_38 x) (by simp only [RowInput.carryA0, RowInput.sumA0]; omega)
  · exact bit (RowInput.assignment_39 x) (by omega)
  · exact bit (RowInput.assignment_40 x) (by
      simp only [RowInput.carryA1, RowInput.sumA1, RowInput.carryA0, RowInput.sumA0]; omega)
  · exact bit (RowInput.assignment_49 x) (by
      simp only [RowInput.carryC0, RowInput.sumC0, RowInput.d1lo]; omega)
  · exact bit (RowInput.assignment_50 x) (by
      simp only [RowInput.carryC1, RowInput.sumC1, RowInput.d1hi, RowInput.carryC0, RowInput.sumC0,
        RowInput.d1lo]; omega)
  · exact bit (RowInput.assignment_65 x) (by omega)
  · exact bit (RowInput.assignment_66 x) (by
      simp only [RowInput.carryA2, RowInput.sumA2, RowInput.a1lo, RowInput.b1lo]; omega)
  · exact bit (RowInput.assignment_67 x) (by omega)
  · exact bit (RowInput.assignment_68 x) (by
      simp only [RowInput.carryA3, RowInput.sumA3, RowInput.a1hi, RowInput.b1hi, RowInput.carryA2,
        RowInput.sumA2, RowInput.a1lo, RowInput.b1lo]; omega)
  · exact bit (RowInput.assignment_75 x) (by
      simp only [RowInput.carryC2, RowInput.sumC2, RowInput.c1lo, RowInput.d2lo]; omega)
  · exact bit (RowInput.assignment_76 x) (by
      simp only [RowInput.carryC3, RowInput.sumC3, RowInput.c1hi, RowInput.d2hi, RowInput.carryC2,
        RowInput.sumC2, RowInput.c1lo, RowInput.d2lo]; omega)
  -- the nine borrow flags (columns 85 + 3 j) hold 1
  all_goals exact bit (n := 1) rfl le_rfl

end Airbender.NonVacuous.Blake2GSpan
