module
public import Proven.Blake2Round.Mask.OneHot
public import Proven.Blake2Round.Mask.RVBodies

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Airbender.Specs.BLAKE3.g Airbender.Specs.BLAKE3.round

/-- The pure one-hot working vector is the scheduled RV working vector. -/
theorem onehot_mixed {control : RV.Word} {r : Nat} (bound : r < 10)
    (mask : control >>> 19 = 1#32 <<< r) (h : Vector RV.Word 8) (e m : Vector RV.Word 16) :
    maskedMixed control h e m = scheduledMixed control r h e m := by
  have first : RV.Delegation.roundMaskBit control 0 = decide (r = 0) := by
    simpa only [Fin.val_zero, eq_comm] using onehot_mask_bits bound mask 0
  rw [maskedMixed, onehot_round bound mask, scheduledMixed, maskedPrepared, first]
  have round : (⟨r % 10, Nat.mod_lt _ (by decide)⟩ : Fin 10) = ⟨r, bound⟩ :=
    Fin.ext (Nat.mod_eq_of_lt bound)
  rw [round]
  by_cases zero : r = 0
  · simp only [zero, decide_true, ↓reduceIte]
  · simp only [zero, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- The complete pure native mask effect is the valid scheduled effect. -/
theorem onehot_body (state : RV.Word) {control : RV.Word} {r : Nat}
    (bound : r < if control.getLsbD 16 then 7 else 10)
    (mask : control >>> 19 = 1#32 <<< r) (h : Vector RV.Word 8) (e m : Vector RV.Word 16) :
    maskedBody state control h e m = scheduledBody state control r h e m := by
  have small : r < 10 := by split at bound <;> omega
  rw [maskedBody, onehot_mixed small mask, onehot_final bound mask, scheduledBody]
  simp only [decide_eq_true_eq]

end Airbender.Blake2Round.Mask.Proofs
