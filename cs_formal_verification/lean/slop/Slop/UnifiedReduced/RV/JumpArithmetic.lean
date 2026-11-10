module
public import Slop.UnifiedReduced.RV.ControlQueries

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

theorem control_intermediate_bounds [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (Word.mk (w 74).val (w 75).val).Bounded ∧ (w 64).val < limbBase := by
  have low := Verification.lookup_of_holds holds ⟨0, by rw [lookup_count]; decide⟩
  op_index at low
  replace low := Verification.range16_bound low
  have high := Verification.lookup_of_holds holds ⟨1, by rw [lookup_count]; decide⟩
  op_index at high
  replace high := Verification.range16_bound high
  have raw := Verification.lookup_of_holds holds ⟨5, by rw [lookup_count]; decide⟩
  op_index at raw
  replace raw := Verification.range16_bound raw
  simpa [Expression.eval, Verification.environment, Word.Bounded] using And.intro (And.intro low high) raw

theorem jump_link [Fact p.Prime] (hp : 196608 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 21 + w 22 = 1) (other : w 23 = 0 ∧ w 24 = 0)
    (initial : (Word.mk (w 0).val (w 1).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec =
      (if w 25 = 1 then 0 else (Word.mk (w 0).val (w 1).val).toBitVec + 4) := by
  have low := Verification.assertion_of_holds holds ⟨12, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨13, by rw [constraint_count]; decide⟩
  op_index at low high
  simp [Expression.eval, Verification.environment,
    other.1, other.2] at low high
  have lowEq : w 0 + 4 = w 74 + 65536 * w 52 := by
    linear_combination low - (w 0 + 4 - w 74 - 65536 * w 52) * selected
  have highEq : w 52 + w 1 = w 75 + 65536 * w 53 := by
    linear_combination high - (w 52 + w 1 - w 75 - 65536 * w 53) * selected
  have carry := boolean_val (local_flags holds 20)
  change (w 52).val ≤ 1 at carry
  have wrap := boolean_val (local_flags holds 21)
  change (w 53).val ≤ 1 at wrap
  have saved := Word.add_of_limbs hp (left := Word.mk (w 0).val (w 1).val)
    (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩) (output := Word.mk (w 74).val (w 75).val)
    initial (by constructor <;> decide) (by constructor <;> decide)
    (control_intermediate_bounds holds).1 (Nat.le_trans carry (by decide)) (Nat.le_trans wrap (by decide))
    (by simpa only [Nat.cast_zero, Nat.cast_ofNat, add_zero, ZMod.natCast_zmod_val] using lowEq)
    (by simpa only [Nat.cast_zero, Nat.cast_ofNat, add_zero, ZMod.natCast_zmod_val] using highEq)
  have writeLow := Verification.assertion_of_holds holds ⟨19, by rw [constraint_count]; decide⟩
  have writeHigh := Verification.assertion_of_holds holds ⟨20, by rw [constraint_count]; decide⟩
  have zeroLow := Verification.assertion_of_holds holds ⟨22, by rw [constraint_count]; decide⟩
  have zeroHigh := Verification.assertion_of_holds holds ⟨23, by rw [constraint_count]; decide⟩
  op_index at writeLow writeHigh zeroLow zeroHigh
  simp [Expression.eval, Verification.environment,
    other.1, other.2] at writeLow writeHigh zeroLow zeroHigh
  rcases local_flags holds 15 with zero | one
  · change w 25 = 0 at zero
    have lo : w 50 = w 74 := by
      simp [zero] at writeLow
      linear_combination -writeLow + (w 74 - w 50) * selected
    have hi : w 51 = w 75 := by
      simp [zero, selected] at writeHigh
      linear_combination -writeHigh
    simpa [zero, lo, hi, Word.toBitVec, Word.value, limbBase] using saved
  · change w 25 = 1 at one
    have lo : w 50 = 0 := by simpa [one] using zeroLow
    have hi : w 51 = 0 := by simpa [one] using zeroHigh
    simp [one, lo, hi, Word.toBitVec, Word.value]

theorem jump_pc {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {words : Nat → BitVec 32} {w : Nat → ZMod p} {base offset final : Word} (indirect : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.tableWith words)))
    (selected : w 21 = (if indirect then 0 else 1) ∧ w 22 = (if indirect then 1 else 0))
    (other : w 23 = 0 ∧ w 24 = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 81 = 0)
    (mapping : base.lo = (w (if indirect then 36 else 0)).val ∧
      base.hi = (w (if indirect then 37 else 1)).val ∧
      w 8 = (offset.lo : ZMod p) ∧ w 9 = (offset.hi : ZMod p) ∧
      final.lo = (w 30).val ∧ final.hi = (w 31).val)
    (baseLoBound : base.lo < limbBase)
    (sourceHiBound : indirect = true → base.hi < limbBase)
    (offsetBound : offset.Bounded)
    (directEven : indirect = false → base.lo % 2 = 0 ∧ offset.lo % 2 = 0)
    (finalHiBound : final.hi < limbBase) :
    final.toBitVec = (if indirect then (base.toBitVec + offset.toBitVec) &&& 0xfffffffe
      else base.toBitVec + offset.toBitVec) ∧ final.toBitVec.toNat % 4 = 0 := by
  have intermediate := control_intermediate_bounds h
  have bounds : (w 74).val < limbBase ∧ (w 75).val < limbBase ∧
      (w 1).val < limbBase ∧ (w 64).val < limbBase :=
    ⟨intermediate.1.1, intermediate.1.2, initial_pc_hi_bound h, intermediate.2⟩
  have family : w 21 + w 22 + w 23 + w 24 = 1 := by
    cases indirect <;> simp [selected.1, selected.2, other.1, other.2]
  have cleanup := (control_lookup_values hp h family binary rom).2.2.2.2.2
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 54) (by
    have flag := local_flags h 22
    change w 54 = 0 ∨ w 54 = 1 at flag
    rcases flag with zero | one
    · simp [zero]
    · simp [one])
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 55) (by
    have flag := local_flags h 23
    change w 55 = 0 ∨ w 55 = 1 at flag
    rcases flag with zero | one
    · simp [zero]
    · simp [one])
  have branch := Verification.assertion_of_holds h
    ⟨15, by rw [constraint_count]; decide⟩
  op_index at branch
  simp [Expression.eval, Verification.environment, other.2] at branch
  have low := Verification.assertion_of_holds h
    ⟨16, by rw [constraint_count]; decide⟩
  op_index at low
  have high := Verification.assertion_of_holds h
    ⟨17, by rw [constraint_count]; decide⟩
  op_index at high
  simp [Expression.eval, Verification.environment, other.1, other.2, branch, hc, hb,
    mapping.2.2.1, mapping.2.2.2.1] at low high
  have baseLo : w (if indirect then 36 else 0) = (base.lo : ZMod p) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have baseHi : w (if indirect then 37 else 1) = (base.hi : ZMod p) := by
    rw [mapping.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (base.lo : ZMod p) + offset.lo = (w 64).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    cases indirect <;> dsimp at baseLo <;>
      simp [selected.1, selected.2, baseLo] at low <;>
      linear_combination low
  have highEq : (c : ZMod p) + base.hi + offset.hi = final.hi + 65536 * b := by
    have finalHi : w 31 = (final.hi : ZMod p) := by
      rw [mapping.2.2.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
    rw [finalHi] at high
    cases indirect <;> dsimp at baseHi <;>
      simp [selected.1, selected.2, baseHi] at high <;>
      linear_combination high
  have baseHiBound : base.hi < limbBase := by
    cases indirect
    · exact mapping.2.1 ▸ bounds.2.2.1
    · exact sourceHiBound rfl
  have baseBound : base.Bounded := ⟨baseLoBound, baseHiBound⟩
  have lowNat : base.lo + offset.lo = (w 64).val + 65536 * c :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by have := offsetBound.1; unfold limbBase at *; omega)
      (by have := bounds.2.2.2; unfold limbBase at *; omega)
      (by exact_mod_cast lowEq)
  have bit1 : (w 64).val / 2 % 2 = 0 := by
    have checked := Verification.assertion_of_holds h
      ⟨18, by rw [constraint_count]; decide⟩
    op_index at checked
    cases indirect <;>
      simp [Expression.eval, Verification.environment, selected.1, selected.2, branch] at checked
    all_goals
      have eq : (((w 64).val / 2 % 2 : Nat) : ZMod p) = 0 := cleanup.1 ▸ checked
      have eqVal := congrArg ZMod.val eq
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
        have := Nat.mod_lt ((w 64).val / 2) (by decide : 0 < 2); omega)] at eqVal
      simpa using eqVal
  have cleaned : final.lo = (w 64).val - (w 64).val % 4 := by
    rw [mapping.2.2.2.2.1, cleanup.2, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2; unfold limbBase at this; omega)]
  have finalBound : final.Bounded :=
    ⟨by rw [cleaned]; exact lt_of_le_of_lt (Nat.sub_le _ _) bounds.2.2.2, finalHiBound⟩
  let raw : Word := ⟨(w 64).val, final.hi⟩
  have rawBound : raw.Bounded := ⟨bounds.2.2.2, finalHiBound⟩
  have sum := Word.add_of_limbs (by omega : 196608 < p)
    (left := base) (right := ⟨0, 0⟩) (immediate := offset) (output := raw)
    baseBound (by constructor <;> decide) offsetBound rawBound (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [raw] using lowEq) (by simpa [raw] using highEq)
  have sumEq : raw.toBitVec = base.toBitVec + offset.toBitVec := by
    simpa [Word.toBitVec, Word.value, limbBase] using sum
  constructor
  · cases indirect
    · have aligned : (w 64).val % 4 = 0 := by
        obtain ⟨baseEven, offsetEven⟩ := directEven rfl
        omega
      have same : final.toBitVec = raw.toBitVec := by
        simp only [Word.toBitVec, Word.value, raw]
        rw [cleaned, aligned, Nat.sub_zero]
      simpa [← same] using sumEq
    · simp only [↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      rw [clear_low_bit_toNat, ← sumEq, Word.toBitVec_toNat rawBound,
        Word.toBitVec_toNat finalBound]
      dsimp [Word.value, limbBase, raw] at *
      omega
  · rw [Word.toBitVec_toNat finalBound]
    dsimp [Word.value, limbBase]
    omega


end Airbender.UnifiedReduced.Proofs.RV
