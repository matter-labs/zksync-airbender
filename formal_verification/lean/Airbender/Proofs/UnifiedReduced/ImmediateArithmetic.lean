import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.JumpArithmetic
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic
set_option warningAsError true

theorem immediate_add_result [Fact p.Prime] (hp : FieldCapacity.NoWrap p 196608)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (selected : w 11 = 1)
    (right : w 42 = 0 ∧ w 43 = 0)
    (leftBound : (Word.mk (w 36).val (w 37).val).Bounded)
    (immediate : (Word.mk (w 8).val (w 9).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec =
      (Word.mk (w 36).val (w 37).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec := by
  have other := UnifiedReduced.Proofs.dispatch_exclusive (by omega) h active 0 selected
  have flags : w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧ w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0 := by
    repeat' apply And.intro
    all_goals first
      | exact other 1 (by decide) | exact other 2 (by decide)
      | exact other 3 (by decide) | exact other 4 (by decide)
      | exact other 5 (by decide) | exact other 6 (by decide)
      | exact other 9 (by decide)
  have low := Verification.assertion_of_holds h ⟨4, by rw [UnifiedReduced.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [UnifiedReduced.constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, flags.1, flags.2.1, flags.2.2.1, flags.2.2.2.1, flags.2.2.2.2.1,
    flags.2.2.2.2.2.1, flags.2.2.2.2.2.2, right.1, right.2] at low high
  have carry := boolean_val (UnifiedReduced.Proofs.local_flags h 21)
  have overflow := boolean_val (UnifiedReduced.Proofs.local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at overflow
  have loEq : ((w 36).val : ZMod p) + 0 + (w 8).val = (w 50).val + 65536 * (w 53).val := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination low
  have hiEq : ((w 53).val : ZMod p) + (w 37).val + 0 + (w 9).val = (w 51).val + 65536 * (w 52).val := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination high
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs
    (left := ⟨(w 36).val, (w 37).val⟩) (right := ⟨0, 0⟩) (immediate := ⟨(w 8).val, (w 9).val⟩)
    (output := ⟨(w 50).val, (w 51).val⟩) hp leftBound (by constructor <;> decide) immediate
    (UnifiedReduced.Proofs.destination_bounds h) (Nat.le_trans carry (by decide)) (Nat.le_trans overflow (by decide))
    (by simpa only [Nat.cast_zero] using loEq) (by simpa only [Nat.cast_zero] using hiEq)

end Airbender.UnifiedReduced.Caller.Proofs
