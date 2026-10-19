import Airbender.Proofs.JumpBranchSlt.Link

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Verification

/-- Native target carries are Boolean, including the RV32 high-limb wrap. -/
theorem pc_carries {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    ∃ c b : Nat, c ≤ 1 ∧ b ≤ 1 ∧ w 50 = (c : ZMod p) ∧ w 44 = (b : ZMod p) := by
  have carry := assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
  have wrap := assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at carry wrap
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 50) (by convert carry using 1; ring)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 44) (by convert wrap using 1; ring)
  exact ⟨c, b, cb, bb, hc, hb⟩

/-- The native packed jump mask fixes JAL/JALR identity as well as selection. -/
theorem jump_identity {w : Nat → ZMod mersenne31Modulus} (indirect : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (mask : (w 12).val = if indirect then 2 else 1) :
    (w 17 = (if indirect then 0 else 1) ∧ w 18 = (if indirect then 1 else 0)) ∧
      (w 19 = 0 ∧ w 20 = 0 ∧ w 21 = 0) := by
  have member : (w 12).val ∈ [1,2] := by cases indirect <;> simp [mask]
  obtain ⟨pair, other⟩ := jump_selectors (by decide) h member
  have packed := assertion_of_holds h ⟨33, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    other.1, other.2.1, other.2.2] at packed
  have fieldMask : w 12 = (if indirect then 2 else 1) := by
    have eq := congrArg (fun n : Nat => (n : ZMod mersenne31Modulus)) mask
    cases indirect <;> simpa only [Bool.false_eq_true, if_false, if_true,
      Nat.cast_ofNat, Nat.cast_one, ZMod.natCast_zmod_val] using eq
  rw [fieldMask] at packed
  refine ⟨?_, other⟩
  cases indirect <;> simp only [Bool.false_eq_true, if_false, if_true] at packed ⊢
  all_goals constructor
  all_goals first | linear_combination -packed + 2 * pair | linear_combination packed - pair

/-- Local target calculation reuses original modular addition and bit cleanup.
    Native scalar/fixed queries derive both output bounds; direct parity and
    source bounds are connected to public decoding/initialized history separately. -/
theorem jump_pc {w : Nat → ZMod mersenne31Modulus} {base offset : Word}
    (indirect : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 17 = (if indirect then 0 else 1) ∧ w 18 = (if indirect then 1 else 0))
    (other : w 19 = 0 ∧ w 20 = 0 ∧ w 21 = 0)
    (mapping : base.lo = (w (if indirect then 22 else 0)).val ∧
      base.hi = (w (if indirect then 23 else 1)).val ∧
      w 9 = (offset.lo : ZMod mersenne31Modulus) ∧ w 10 = (offset.hi : ZMod mersenne31Modulus))
    (baseBound : base.Bounded) (offsetBound : offset.Bounded)
    (directEven : indirect = false → base.lo % 2 = 0 ∧ offset.lo % 2 = 0) :
    (Word.mk (w 13).val (w 14).val).toBitVec =
      (if indirect then (base.toBitVec + offset.toBitVec) &&& 0xfffffffe
      else base.toBitVec + offset.toBitVec) ∧
    (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 := by
  have cleanup := fixed_effects h
  obtain ⟨c, b, cb, bb, hc, hb⟩ := pc_carries h
  have branch := assertion_of_holds h ⟨24, by rw [constraint_count]; decide⟩
  have taken := assertion_of_holds h ⟨25, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    other.2.2] at branch taken
  have low := assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨32, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    other.1, other.2.1, branch, taken, hc, hb, mapping.2.2.1, mapping.2.2.2] at low high
  have baseLo : w (if indirect then 22 else 0) = (base.lo : ZMod mersenne31Modulus) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have baseHi : w (if indirect then 23 else 1) = (base.hi : ZMod mersenne31Modulus) := by
    rw [mapping.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (base.lo : ZMod mersenne31Modulus) + offset.lo = (w 42).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    cases indirect <;> dsimp at baseLo <;>
      simp [selected.1, selected.2, baseLo] at low <;> linear_combination low
  have highEq : (c : ZMod mersenne31Modulus) + base.hi + offset.hi = (w 43).val + 65536 * b := by
    simp only [ZMod.natCast_zmod_val]
    cases indirect <;> dsimp at baseHi <;>
      simp [selected.1, selected.2, baseHi] at high <;> linear_combination high
  have lowNat : base.lo + offset.lo = (w 42).val + 65536 * c :=
    bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (by have := baseBound.1; have := offsetBound.1; dsimp [limbBase] at *; change _ < 2147483647; omega)
      (by have := cleanup.cleanupBound; change _ < 2147483647; omega)
      (by exact_mod_cast lowEq)
  have bit1 : (w 42).val / 2 % 2 = 0 := by
    have checked := assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
    cases indirect <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
        selected.1, selected.2, taken] at checked
    all_goals
      have eq : (((w 42).val / 2 % 2 : Nat) : ZMod mersenne31Modulus) = 0 := cleanup.bit1 ▸ checked
      have eqVal := congrArg ZMod.val eq
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
        have := Nat.mod_lt ((w 42).val / 2) (by decide : 0 < 2); dsimp [mersenne31Modulus]; omega)] at eqVal
      simpa using eqVal
  have finalLo : w 13 = w 48 := by
    have eq := assertion_of_holds h ⟨27, by rw [constraint_count]; decide⟩
    cases indirect <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
        selected.1, selected.2, other.1, other.2.1, branch, taken] at eq <;>
      linear_combination -eq
  have finalHi : w 14 = w 43 := by
    have eq := assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
    cases indirect <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
        selected.1, selected.2, other.1, other.2.1, branch, taken] at eq <;>
      linear_combination -eq
  have rounded : 4 * ((w 42).val / 4) ≤ (w 42).val := by
    exact Nat.mul_div_le _ _
  have cleaned : (w 13).val = (w 42).val - (w 42).val % 4 := by
    rw [finalLo, cleanup.cleaned, ZMod.val_natCast_of_lt (by
      have bound := lt_of_le_of_lt rounded cleanup.cleanupBound
      exact lt_trans bound (by decide : 65536 < mersenne31Modulus))]
    omega
  have finalBound : (Word.mk (w 13).val (w 14).val).Bounded :=
    ⟨by change (w 13).val < 65536; rw [cleaned]
        exact lt_of_le_of_lt (Nat.sub_le _ _) cleanup.cleanupBound,
      by change _ < 65536; rw [finalHi]; exact candidate_high_bound h⟩
  let raw : Word := ⟨(w 42).val, (w 43).val⟩
  have rawBound : raw.Bounded := ⟨cleanup.cleanupBound, candidate_high_bound h⟩
  have sum := Word.add_of_limbs (by decide : 196608 < mersenne31Modulus)
    (left := base) (right := ⟨0, 0⟩) (immediate := offset) (output := raw)
    baseBound (by constructor <;> decide) offsetBound rawBound
    (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [raw] using lowEq) (by simpa [raw] using highEq)
  have sumEq : raw.toBitVec = base.toBitVec + offset.toBitVec := by
    simpa [Word.toBitVec, Word.value, limbBase] using sum
  constructor
  · cases indirect
    · have aligned : (w 42).val % 4 = 0 := by
        obtain ⟨baseEven, offsetEven⟩ := directEven rfl
        omega
      have same : (Word.mk (w 13).val (w 14).val).toBitVec = raw.toBitVec := by
        simp only [Word.toBitVec, Word.value, raw, finalHi]
        rw [cleaned, aligned, Nat.sub_zero]
      simpa [← same] using sumEq
    · simp only [↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      rw [clear_low_bit_toNat, ← sumEq, Word.toBitVec_toNat rawBound,
        Word.toBitVec_toNat finalBound]
      dsimp [Word.value, limbBase, raw] at *
      rw [finalHi]
      omega
  · rw [Word.toBitVec_toNat finalBound]
    dsimp [Word.value, limbBase]
    rw [finalHi]
    omega

end Airbender.JumpBranchSlt.Proofs
