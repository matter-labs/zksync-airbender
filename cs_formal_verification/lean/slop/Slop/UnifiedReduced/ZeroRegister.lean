module
public import Slop.UnifiedReduced.Trace
public import Slop.Trace.RowHistory
public import Human.Circuits.UnifiedReduced.Decoder
public import Slop.JumpBranchSlt
public import Slop.ShiftBinop
public import Slop.UnifiedReduced

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem zero_operands_result [Fact p.Prime] (hp : 196608 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (selected : w 11 = 1)
    (operands : w 36 = 0 ∧ w 37 = 0 ∧ w 42 = 0 ∧ w 43 = 0 ∧ w 8 = 0 ∧ w 9 = 0) :
    (⟨(w 50).val, (w 51).val⟩ : Word).toBitVec = 0 := by
  have other := dispatch_exclusive (by omega) h active 0 selected
  have flags : w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧
      w 16 = 0 ∧ w 17 = 0 ∧ w 20 = 0 := by
    repeat' apply And.intro
    all_goals first
      | exact other 1 (by decide) | exact other 2 (by decide)
      | exact other 3 (by decide) | exact other 4 (by decide)
      | exact other 5 (by decide) | exact other 6 (by decide)
      | exact other 9 (by decide)
  have low := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  op_index at low high
  simp [Expression.eval, Verification.environment,
    selected, flags.1, flags.2.1, flags.2.2.1, flags.2.2.2.1, flags.2.2.2.2.1,
    flags.2.2.2.2.2.1, flags.2.2.2.2.2.2, operands.1, operands.2.1,
    operands.2.2.1, operands.2.2.2.1, operands.2.2.2.2.1, operands.2.2.2.2.2] at low high
  have carry := boolean_val (local_flags h 21)
  have overflow := boolean_val (local_flags h 20)
  change (w 53).val ≤ 1 at carry
  change (w 52).val ≤ 1 at overflow
  have loEq : (0 : ZMod p) + 0 + 0 = (w 50).val + 65536 * (w 53).val := by
    simp only [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    linear_combination low
  have hiEq : ((w 53).val : ZMod p) + 0 + 0 + 0 = (w 51).val + 65536 * (w 52).val := by
    simp only [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    linear_combination high
  have zeroBound : (⟨0, 0⟩ : Word).Bounded := ⟨by decide, by decide⟩
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs
    (left := ⟨0, 0⟩) (right := ⟨0, 0⟩) (immediate := ⟨0, 0⟩)
    (output := ⟨(w 50).val, (w 51).val⟩) hp zeroBound zeroBound zeroBound
    (destination_bounds h) (Nat.le_trans carry (by decide)) (Nat.le_trans overflow (by decide))
    (by simpa only [Nat.cast_zero] using loEq) (by simpa only [Nat.cast_zero] using hiEq)

end Airbender.UnifiedReduced.Proofs
