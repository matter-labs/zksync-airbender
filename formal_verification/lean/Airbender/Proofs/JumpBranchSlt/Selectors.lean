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

/-- Native one-hot selection leaves only three write routes. Calculations use
    canonical selector residues; no chosen selector or result is supplied. -/
theorem write_routes {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val ∈ [1,2,4,8,16]) :
    (w 17 + w 18 = 0 ∧ w 19 + w 20 = 0) ∨
    (w 17 + w 18 = 1 ∧ w 19 + w 20 = 0) ∨
    (w 17 + w 18 = 0 ∧ w 19 + w 20 = 1) := by
  have total := (selector_partition (by omega) native mask).1
  have b0 : (w 17).val ≤ 1 := selector_bound native ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound native ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound native ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound native ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound native ⟨4, by decide⟩
  have natural : (w 17).val + (w 18).val + (w 19).val + (w 20).val + (w 21).val = 1 := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using total
  have choices :
      ((w 17).val + (w 18).val = 0 ∧ (w 19).val + (w 20).val = 0) ∨
      ((w 17).val + (w 18).val = 1 ∧ (w 19).val + (w 20).val = 0) ∨
      ((w 17).val + (w 18).val = 0 ∧ (w 19).val + (w 20).val = 1) := by omega
  rcases choices with zero | link | comparison
  · left; constructor
    · simpa only [Nat.cast_add, Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero.1
    · simpa only [Nat.cast_add, Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero.2
  · right; left; constructor
    · simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) link.1
    · simpa only [Nat.cast_add, Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) link.2
  · right; right; constructor
    · simpa only [Nat.cast_add, Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) comparison.1
    · simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) comparison.2

/-- Native jump masks recover both jump selection and all inactive operation bits. -/
theorem jump_selectors {p : Nat} [Fact p.Prime] (hp : 32 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val ∈ [1,2]) :
    w 17 + w 18 = 1 ∧ w 19 = 0 ∧ w 20 = 0 ∧ w 21 = 0 := by
  have b0 : (w 17).val ≤ 1 := selector_bound h ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound h ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound h ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound h ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound h ⟨4, by decide⟩
  have packed := Verification.assertion_of_holds h ⟨33, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at packed
  have natural : (w 17).val + 2 * (w 18).val + 4 * (w 19).val +
      8 * (w 20).val + 16 * (w 21).val = (w 12).val := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (ZMod.val_lt _)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination packed
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at mask
  have pair : (w 17).val + (w 18).val = 1 := by omega
  have zero2 : (w 19).val = 0 := by omega
  have zero3 : (w 20).val = 0 := by omega
  have zero4 : (w 21).val = 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val] using
      congrArg (fun n : Nat => (n : ZMod p)) pair
  all_goals first
    | simpa only [Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero2
    | simpa only [Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero3
    | simpa only [Nat.cast_zero, ZMod.natCast_zmod_val] using
        congrArg (fun n : Nat => (n : ZMod p)) zero4

/-- Actual mask four/eight fixes register/immediate comparison identity. -/
theorem comparison_selectors {p : Nat} [Fact p.Prime] (hp : 32 < p)
    {w : Nat → ZMod p} (immediate : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val = if immediate then 8 else 4) :
    (w 19 = (if immediate then 0 else 1) ∧ w 20 = (if immediate then 1 else 0)) ∧
      (w 17 = 0 ∧ w 18 = 0 ∧ w 21 = 0) := by
  have b0 : (w 17).val ≤ 1 := selector_bound h ⟨0, by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound h ⟨1, by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound h ⟨2, by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound h ⟨3, by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound h ⟨4, by decide⟩
  have packed := Verification.assertion_of_holds h ⟨33, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at packed
  have natural : (w 17).val + 2 * (w 18).val + 4 * (w 19).val +
      8 * (w 20).val + 16 * (w 21).val = (w 12).val := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (ZMod.val_lt _)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    linear_combination packed
  have valEq (i n : Nat) (eq : (w i).val = n) : w i = (n : ZMod p) := by
    rw [← eq]; exact (ZMod.natCast_zmod_val _).symm
  cases immediate <;> simp only [Bool.false_eq_true,if_false,if_true] at mask ⊢
  · exact ⟨⟨by simpa using valEq 19 1 (by omega),by simpa using valEq 20 0 (by omega)⟩,
      by simpa using valEq 17 0 (by omega),by simpa using valEq 18 0 (by omega),
      by simpa using valEq 21 0 (by omega)⟩
  · exact ⟨⟨by simpa using valEq 19 0 (by omega),by simpa using valEq 20 1 (by omega)⟩,
      by simpa using valEq 17 0 (by omega),by simpa using valEq 18 0 (by omega),
      by simpa using valEq 21 0 (by omega)⟩

/-- Packed mask sixteen recovers the branch selector and every inactive family. -/
theorem branch_selectors {p : Nat} [Fact p.Prime] (hp : 32 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val = 16) :
    w 21 = 1 ∧ w 17 = 0 ∧ w 18 = 0 ∧ w 19 = 0 ∧ w 20 = 0 := by
  have b0 : (w 17).val ≤ 1 := selector_bound h ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := selector_bound h ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := selector_bound h ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := selector_bound h ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := selector_bound h ⟨4,by decide⟩
  have packed := Verification.assertion_of_holds h ⟨33,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,Verification.environment] at packed
  have natural : (w 17).val + 2*(w 18).val + 4*(w 19).val + 8*(w 20).val +
      16*(w 21).val = (w 12).val := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p) (by omega) (ZMod.val_lt _)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val]
    linear_combination packed
  have valEq (i n : Nat) (eq : (w i).val = n) : w i = (n : ZMod p) := by
    rw [← eq]; exact (ZMod.natCast_zmod_val _).symm
  exact ⟨by simpa using valEq 21 1 (by omega),by simpa using valEq 17 0 (by omega),
    by simpa using valEq 18 0 (by omega),by simpa using valEq 19 0 (by omega),
    by simpa using valEq 20 0 (by omega)⟩

end Airbender.JumpBranchSlt.Proofs
