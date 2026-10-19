import Airbender.Proofs.MulDiv.Results

namespace Airbender.MulDiv.Proofs
open Arithmetic

theorem selected_bound {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (selectedWord w).Bounded := by
  have ranges := local_ranges native
  have bit := boolean_values native 18 (by simp)
  have either : (w 18).val = 0 ∨ (w 18).val = 1 := by omega
  rcases either with zero | one
  · have flag : w 18 = 0 := by rw [← ZMod.natCast_zmod_val (w 18),zero]; rfl
    rw [selected_raw native false flag]
    exact ⟨ranges 25 (by simp),ranges 26 (by simp)⟩
  · have flag : w 18 = 1 := by rw [← ZMod.natCast_zmod_val (w 18),one]; rfl
    rw [selected_raw native true flag]
    exact ⟨ranges 23 (by simp),ranges 24 (by simp)⟩

/-- Native range queries and the actual decoded zero flag bound both writes. -/
theorem written_limb_bounds {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (flag : w 8 = 0 ∨ w 8 = 1) : (writtenWord w).Bounded := by
  rcases flag with zero | one
  · rw [written_mask native false zero]
    exact selected_bound native
  · rw [written_mask native true one]
    change (⟨0,0⟩ : Word).Bounded
    constructor <;> decide

end Airbender.MulDiv.Proofs
