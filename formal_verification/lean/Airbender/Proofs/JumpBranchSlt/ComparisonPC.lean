import Airbender.Proofs.JumpBranchSlt.Target

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Verification

/-- Comparison rows route the raw PC+4 candidate directly to the output.
    Actual scalar queries bound both limbs, including RV32 high-limb wrap. -/
theorem comparison_pc {w : Nat → ZMod mersenne31Modulus}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 19 + w 20 = 1) (other : w 17 = 0 ∧ w 18 = 0 ∧ w 21 = 0)
    (initialBound : (Word.mk (w 0).val (w 1).val).Bounded)
    (initialAligned : (w 0).val % 4 = 0) :
    (Word.mk (w 13).val (w 14).val).toBitVec =
      (Word.mk (w 0).val (w 1).val).toBitVec + 4 ∧
    (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 := by
  obtain ⟨c,b,cb,bb,hc,hb⟩ := pc_carries h
  have notTaken := assertion_of_holds h ⟨24,by rw [constraint_count]; decide⟩
  have taken := assertion_of_holds h ⟨25,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    other.2.2] at notTaken taken
  have low := assertion_of_holds h ⟨31,by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨32,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    other.1,other.2.1,notTaken,taken,hc,hb] at low high
  have lowEq : w 0 + 4 = ((w 42).val : ZMod mersenne31Modulus) + 65536*c := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination low - (w 0 + 4 - w 42) * selected
  have highEq : (c : ZMod mersenne31Modulus) + w 1 = (w 43).val + 65536*b := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination high - (w 1 - w 43) * selected
  have finalLo : w 13 = w 42 := by
    have eq := assertion_of_holds h ⟨27,by rw [constraint_count]; decide⟩
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
      other.1,other.2.1,notTaken,taken] at eq
    linear_combination -eq + w 42 * selected
  have finalHi : w 14 = w 43 := by
    have eq := assertion_of_holds h ⟨28,by rw [constraint_count]; decide⟩
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
      other.1,other.2.1,notTaken,taken] at eq
    linear_combination -eq + w 43 * selected
  have bounds : (Word.mk (w 42).val (w 43).val).Bounded :=
    ⟨range16_bound (lookup_of_holds h ⟨4,by rw [lookup_count]; decide⟩),
      candidate_high_bound h⟩
  have sum := Word.add_of_limbs (by decide : 196608 < mersenne31Modulus)
    (left := ⟨(w 0).val,(w 1).val⟩) (right := ⟨0,0⟩) (immediate := ⟨4,0⟩)
    initialBound (by constructor <;> decide) (by constructor <;> decide) bounds
    (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa using lowEq) (by simpa using highEq)
  have lowNat : (w 0).val + 4 = (w 42).val + 65536*c :=
    bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (by have := initialBound.1; dsimp [limbBase] at *; change _ < 2147483647; omega)
      (by have := bounds.1; dsimp [limbBase] at *; change _ < 2147483647; omega)
      (by simpa only [ZMod.natCast_zmod_val,Nat.cast_add,Nat.cast_ofNat,Nat.cast_mul] using lowEq)
  rw [finalLo,finalHi]
  constructor
  · simpa [Word.toBitVec,Word.value,limbBase] using sum
  · rw [Word.toBitVec_toNat bounds]
    dsimp [Word.value,limbBase]
    omega

end Airbender.JumpBranchSlt.Proofs
