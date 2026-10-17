import Airbender.Review.Circuits.AddSub.Model
import Airbender.Proofs.AddSub.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.AddSub.Proofs
open Reference.RiscV

private theorem selector_bound {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (i : Fin 8) : (w (17 + i.val)).val ≤ 1 := by
  have bit := Verification.assertion_of_holds h
    ⟨i.val, by rw [constraint_count]; omega⟩
  fin_cases i
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound
  · simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment] at bit ⊢
    obtain ⟨n, bound, eq⟩ := Arithmetic.boolean_nat (by convert bit using 1; ring)
    rw [eq]
    simpa only [ZMod.val_natCast] using le_trans (Nat.mod_le n p) bound

theorem selected_bits {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {input : Sail.Input} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : w 12 = (decodedMask input : ZMod p)) (nonzero : input.rd ≠ Sail.zeroRegister) :
    w 17 = (if input.row.opcode = .add then 1 else 0) ∧
    w 18 = (if input.row.opcode = .addi then 1 else 0) ∧
    w 19 = (if input.row.opcode = .sub then 1 else 0) ∧
    w 20 = (if input.row.opcode = .lui then 1 else 0) ∧
    w 21 = (if input.row.opcode = .auipc then 1 else 0) ∧
    w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 := by
  have b0 : (w 17).val ≤ 1 := selector_bound h ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound h ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound h ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound h ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound h ⟨4, by decide⟩
  have b5 : (w 22).val ≤ 1 := selector_bound h ⟨5, by decide⟩
  have b6 : (w 23).val ≤ 1 := selector_bound h ⟨6, by decide⟩
  have b7 : (w 24).val ≤ 1 := selector_bound h ⟨7, by decide⟩
  have packed := Verification.assertion_of_holds h ⟨34, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mask] at packed
  have equation : w 17 + 2 * w 18 + 4 * w 19 + 8 * w 20 + 16 * w 21 +
      32 * w 22 + 64 * w 23 + 128 * w 24 = (decodedMask input : ZMod p) := by
    linear_combination packed
  have maskBound : decodedMask input < p := by
    cases hop : input.row.opcode <;> simp [decodedMask, nonzero, hop] <;> omega
  have natural : (w 17).val + 2 * (w 18).val + 4 * (w 19).val + 8 * (w 20).val +
      16 * (w 21).val + 32 * (w 22).val + 64 * (w 23).val + 128 * (w 24).val =
      decodedMask input := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) maskBound
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using equation
  cases hop : input.row.opcode
  all_goals
    simp only [decodedMask, nonzero, if_false, hop] at natural
    simp only [reduceCtorEq, if_true, if_false]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      apply ZMod.val_injective p
      simp only [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < p by omega)]
      omega

end Airbender.AddSub.Proofs
