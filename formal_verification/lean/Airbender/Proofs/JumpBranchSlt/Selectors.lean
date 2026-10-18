import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Proofs.JumpBranchSlt.ArtifactChecks
import Airbender.Proofs.Constraints
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.JumpBranchSlt.Proofs

private theorem selector_bound {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (i : Fin 5) : (w (17 + i.val)).val ≤ 1 := by
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


theorem selector_partition {p : Nat} [Fact p.Prime] (hp : 31 < p)
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val ∈ [1, 2, 4, 8, 16]) :
    w 17 + w 18 + w 19 + w 20 + w 21 = 1 ∧
    (w 17 + w 18 = 0 ∨ w 17 + w 18 = 1) ∧
    (w 17 + w 18 + w 21 = 0 ∨ w 17 + w 18 + w 21 = 1) := by
  have b0 : (w 17).val ≤ 1 := selector_bound holds ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound holds ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound holds ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound holds ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound holds ⟨4, by decide⟩
  have packed := Verification.assertion_of_holds holds ⟨33, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at packed
  have natural : (w 17).val + 2 * (w 18).val + 4 * (w 19).val +
      8 * (w 20).val + 16 * (w 21).val = (w 12).val := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (ZMod.val_lt _)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination packed
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at mask
  have total : (w 17).val + (w 18).val + (w 19).val + (w 20).val + (w 21).val = 1 := by
    omega
  have pair : (w 17).val + (w 18).val = 0 ∨ (w 17).val + (w 18).val = 1 := by omega
  have triple : (w 17).val + (w 18).val + (w 21).val = 0 ∨
      (w 17).val + (w 18).val + (w 21).val = 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
      congrArg (fun n : Nat => (n : ZMod p)) total
  · rcases pair with zero | one
    · left; simpa only [Nat.cast_add, Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero
    · right; simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) one
  · rcases triple with zero | one
    · left; simpa only [Nat.cast_add, Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero
    · right; simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) one

/-- All native packed masks are bounded, before any setup row is selected. -/
theorem packed_mask_bound {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 12).val ≤ 31 := by
  have b0 : (w 17).val ≤ 1 := selector_bound h ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound h ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound h ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound h ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound h ⟨4, by decide⟩
  have packed := Verification.assertion_of_holds h ⟨33, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at packed
  let n := (w 17).val + 2 * (w 18).val + 4 * (w 19).val + 8 * (w 20).val +
    16 * (w 21).val
  have bound : n ≤ 31 := by dsimp [n]; omega
  have equation : (n : ZMod p) = w 12 := by
    dsimp [n]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination packed
  have same := congrArg ZMod.val equation
  rw [ZMod.val_natCast_of_lt (by omega : n < p)] at same
  omega

end Airbender.JumpBranchSlt.Proofs
