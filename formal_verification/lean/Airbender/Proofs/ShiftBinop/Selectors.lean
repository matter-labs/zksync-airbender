import Airbender.Proofs.ShiftBinop.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Mersenne31
import Mathlib.Tactic.FinCases

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Booleanity comes from the first six actual native equations. -/
theorem selector_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (slot : Fin 6) : (w (17 + slot.val)).val ≤ 1 := by
  have bit := assertion_of_holds holds ⟨slot.val, by rw [constraint_count]; omega⟩
  fin_cases slot
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit ⊢
    obtain ⟨n, bound, same⟩ := boolean_nat (x := w 17) (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit ⊢
    obtain ⟨n, bound, same⟩ := boolean_nat (x := w 18) (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit ⊢
    obtain ⟨n, bound, same⟩ := boolean_nat (x := w 19) (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit ⊢
    obtain ⟨n, bound, same⟩ := boolean_nat (x := w 20) (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit ⊢
    obtain ⟨n, bound, same⟩ := boolean_nat (x := w 21) (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit ⊢
    obtain ⟨n, bound, same⟩ := boolean_nat (x := w 22) (by linear_combination bit)
    rw [same]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n mersenne31Modulus) bound

/-- The packed mask is bounded by its actual six Boolean bits. -/
theorem packed_mask_bound {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    (w 12).val ≤ 63 := by
  have b0 : (w 17).val ≤ 1 := selector_bounds holds ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bounds holds ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bounds holds ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bounds holds ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bounds holds ⟨4, by decide⟩
  have b5 : (w 22).val ≤ 1 := selector_bounds holds ⟨5, by decide⟩
  have packed := assertion_of_holds holds ⟨47, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at packed
  let n := (w 17).val + 2 * (w 18).val + 4 * (w 19).val + 8 * (w 20).val +
    16 * (w 21).val + 32 * (w 22).val
  have bound : n ≤ 63 := by dsimp [n]; omega
  have field : (n : ZMod mersenne31Modulus) = w 12 := by
    dsimp [n]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination packed
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt (by change n < 2147483647; omega)] at natural
  omega

/-- Exact ordinary operation bits follow from the accepted packed mask, not a
    separate Boolean-selector or table-routing premise. -/
theorem selected_bits {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (op : Operation) (immediate : Bool)
    (mask : w 12 = ((op.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus)) :
    w 17 = (if op = .sll then 1 else 0) ∧
    w 18 = (if op = .srl then 1 else 0) ∧
    w 19 = (if op = .sra then 1 else 0) ∧
    w 20 = (if op.isBinary then 1 else 0) ∧ w 21 = 0 ∧
    w 22 = (if immediate then 1 else 0) := by
  have b0 : (w 17).val ≤ 1 := selector_bounds holds ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bounds holds ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bounds holds ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bounds holds ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bounds holds ⟨4, by decide⟩
  have b5 : (w 22).val ≤ 1 := selector_bounds holds ⟨5, by decide⟩
  have packed := assertion_of_holds holds ⟨47, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at packed
  have field : (((w 17).val + 2 * (w 18).val + 4 * (w 19).val + 8 * (w 20).val +
      16 * (w 21).val + 32 * (w 22).val : Nat) : ZMod mersenne31Modulus) =
      ((op.mask + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] at mask ⊢
    linear_combination packed + mask
  have natural := congrArg ZMod.val field
  rw [ZMod.val_natCast_of_lt (by change _ < 2147483647; omega)] at natural
  have maskBound : op.mask + (if immediate then 32 else 0) < mersenne31Modulus := by
    cases op <;> cases immediate <;> decide
  rw [ZMod.val_natCast_of_lt maskBound] at natural
  cases op <;> cases immediate
  all_goals
    simp [Operation.mask, Operation.isBinary] at natural ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      apply ZMod.val_injective mersenne31Modulus
      simp only [ZMod.val_zero, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (show 1 < mersenne31Modulus by decide)]
      omega

end Airbender.ShiftBinop.Proofs
