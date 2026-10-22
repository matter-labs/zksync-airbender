import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.ControlQueries
import Airbender.Proofs.JumpBranchSlt.Jump

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem control_intermediate_bounds [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (Word.mk (w 78).val (w 79).val).Bounded ∧ (w 81).val < limbBase := by
  have low := Verification.range16_bound (Verification.lookup_of_holds holds ⟨0, by rw [lookup_count]; decide⟩)
  have high := Verification.range16_bound (Verification.lookup_of_holds holds ⟨1, by rw [lookup_count]; decide⟩)
  have raw := Verification.range16_bound (Verification.lookup_of_holds holds ⟨5, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment, Word.Bounded] using And.intro (And.intro low high) raw

theorem jump_link [Fact p.Prime] (hp : FieldCapacity.NoWrap p 196608)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 21 + w 22 = 1) (other : w 23 = 0 ∧ w 24 = 0)
    (initial : (Word.mk (w 0).val (w 1).val).Bounded) :
    (Word.mk (w 50).val (w 51).val).toBitVec =
      (if w 25 = 1 then 0 else (Word.mk (w 0).val (w 1).val).toBitVec + 4) := by
  have low := Verification.assertion_of_holds holds ⟨12, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨13, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    other.1, other.2] at low high
  have lowEq : w 0 + 4 = w 78 + 65536 * w 52 := by
    linear_combination low - (w 0 + 4 - w 78 - 65536 * w 52) * selected
  have highEq : w 52 + w 1 = w 79 + 65536 * w 53 := by
    linear_combination high - (w 52 + w 1 - w 79 - 65536 * w 53) * selected
  have carry := boolean_val (local_flags holds 20)
  change (w 52).val ≤ 1 at carry
  have wrap := boolean_val (local_flags holds 21)
  change (w 53).val ≤ 1 at wrap
  have saved := Word.add_of_limbs hp (left := Word.mk (w 0).val (w 1).val)
    (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩) (output := Word.mk (w 78).val (w 79).val)
    initial (by constructor <;> decide) (by constructor <;> decide)
    (control_intermediate_bounds holds).1 (Nat.le_trans carry (by decide)) (Nat.le_trans wrap (by decide))
    (by simpa only [Nat.cast_zero, Nat.cast_ofNat, add_zero, ZMod.natCast_zmod_val] using lowEq)
    (by simpa only [Nat.cast_zero, Nat.cast_ofNat, add_zero, ZMod.natCast_zmod_val] using highEq)
  have gate := Verification.assertion_of_holds holds ⟨19, by rw [constraint_count]; decide⟩
  have notSlt := Verification.assertion_of_holds holds ⟨20, by rw [constraint_count]; decide⟩
  have mask := Verification.assertion_of_holds holds ⟨21, by rw [constraint_count]; decide⟩
  have writeLow := Verification.assertion_of_holds holds ⟨22, by rw [constraint_count]; decide⟩
  have writeHigh := Verification.assertion_of_holds holds ⟨23, by rw [constraint_count]; decide⟩
  have zeroLow := Verification.assertion_of_holds holds ⟨25, by rw [constraint_count]; decide⟩
  have zeroHigh := Verification.assertion_of_holds holds ⟨26, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, other.1, other.2] at gate notSlt mask writeLow writeHigh zeroLow zeroHigh
  have noSlt : w 84 = 0 := notSlt
  have writesGate : w 83 = 1 - w 25 := by
    linear_combination gate + selected
  have maskedGate : w 85 = w 25 := by
    linear_combination mask
  rcases local_flags holds 15 with zero | one
  · change w 25 = 0 at zero
    have writes : w 83 = 1 := by simpa [zero] using writesGate
    have lo : w 50 = w 78 := by rw [writes, noSlt] at writeLow; linear_combination -writeLow
    have hi : w 51 = w 79 := by
      simp only [writes, one_ne_zero, false_or] at writeHigh
      linear_combination -writeHigh
    simpa [zero, lo, hi, Word.toBitVec, Word.value, limbBase] using saved
  · change w 25 = 1 at one
    have masked : w 85 = 1 := maskedGate.trans one
    have lo : w 50 = 0 := by simpa [masked] using zeroLow
    have hi : w 51 = 0 := by simpa [masked] using zeroHigh
    simp [one, lo, hi, Word.toBitVec, Word.value]

theorem comparison_pc [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 1 ∧ w 24 = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 87 = 0)
    (initial : (Word.mk (w 0).val (w 1).val).Bounded)
    (aligned : (w 0).val % 4 = 0) :
    (Word.mk (w 30).val (w 31).val).toBitVec = (Word.mk (w 0).val (w 1).val).toBitVec + 4 := by
  have rawBound := (control_intermediate_bounds h).2
  have cleanup := (control_lookup_values hp h (by simp [selected]) binary rom).2.2.2.2.2.2
  have carry := boolean_val (local_flags h 22)
  have wrap := boolean_val (local_flags h 23)
  change (w 54).val ≤ 1 at carry
  change (w 55).val ≤ 1 at wrap
  have branch := Verification.assertion_of_holds h ⟨15, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨16, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨17, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2.1, selected.2.2.1, selected.2.2.2] at branch low high
  have lowEq : ((w 0).val : ZMod p) + 4 = (w 81).val + 65536 * (w 54).val := by
    simp only [ZMod.natCast_zmod_val]
    rw [branch] at low
    linear_combination low
  have highEq : ((w 54).val : ZMod p) + (w 1).val = (w 31).val + 65536 * (w 55).val := by
    simp only [ZMod.natCast_zmod_val]
    rw [branch] at high
    linear_combination high
  have lowNat : (w 0).val + 4 = (w 81).val + 65536 * (w 54).val :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by have bound := initial.1; dsimp [limbBase] at bound; omega)
      (by dsimp [limbBase] at rawBound; omega) (by exact_mod_cast lowEq)
  have rawAligned : (w 81).val % 4 = 0 := by omega
  have finalLo : (w 30).val = (w 81).val := by
    rw [cleanup, rawAligned, Nat.sub_zero, ZMod.val_natCast_of_lt (by dsimp [limbBase] at rawBound; omega)]
  have result := Word.add_of_limbs (by omega : 196608 < p)
    (left := Word.mk (w 0).val (w 1).val) (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩)
    (output := Word.mk (w 30).val (w 31).val) initial
    (by constructor <;> decide) (by constructor <;> decide)
    ⟨finalLo ▸ rawBound, (pc_bounds h).2⟩
    (Nat.le_trans carry (by decide)) (Nat.le_trans wrap (by decide))
    (by simpa [finalLo] using lowEq) (by simpa using highEq)
  simpa [Word.toBitVec, Word.value, limbBase] using result

theorem jump_pc {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p} {base offset final : Word} (indirect : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 21 = (if indirect then 0 else 1) ∧ w 22 = (if indirect then 1 else 0))
    (other : w 23 = 0 ∧ w 24 = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (rom : w 87 = 0)
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
  have bounds : (w 78).val < limbBase ∧ (w 79).val < limbBase ∧
      (w 1).val < limbBase ∧ (w 81).val < limbBase :=
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
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.2] at branch
  have low := Verification.assertion_of_holds h
    ⟨16, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h
    ⟨17, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.1, other.2, branch, hc, hb,
    mapping.2.2.1, mapping.2.2.2.1] at low high
  have baseLo : w (if indirect then 36 else 0) = (base.lo : ZMod p) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have baseHi : w (if indirect then 37 else 1) = (base.hi : ZMod p) := by
    rw [mapping.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (base.lo : ZMod p) + offset.lo = (w 81).val + 65536 * c := by
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
  have lowNat : base.lo + offset.lo = (w 81).val + 65536 * c :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by have := offsetBound.1; unfold limbBase at *; omega)
      (by have := bounds.2.2.2; unfold limbBase at *; omega)
      (by exact_mod_cast lowEq)
  have bit1 : (w 81).val / 2 % 2 = 0 := by
    have checked := Verification.assertion_of_holds h
      ⟨18, by rw [constraint_count]; decide⟩
    cases indirect <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected.1, selected.2, branch] at checked
    all_goals
      have eq : (((w 81).val / 2 % 2 : Nat) : ZMod p) = 0 := cleanup.1 ▸ checked
      have eqVal := congrArg ZMod.val eq
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
        have := Nat.mod_lt ((w 81).val / 2) (by decide : 0 < 2); omega)] at eqVal
      simpa using eqVal
  have cleaned : final.lo = (w 81).val - (w 81).val % 4 := by
    rw [mapping.2.2.2.2.1, cleanup.2, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2; unfold limbBase at this; omega)]
  have finalBound : final.Bounded :=
    ⟨by rw [cleaned]; exact lt_of_le_of_lt (Nat.sub_le _ _) bounds.2.2.2, finalHiBound⟩
  let raw : Word := ⟨(w 81).val, final.hi⟩
  have rawBound : raw.Bounded := ⟨bounds.2.2.2, finalHiBound⟩
  have sum := Word.add_of_limbs (by omega : 196608 < p)
    (left := base) (right := ⟨0, 0⟩) (immediate := offset) (output := raw)
    baseBound (by constructor <;> decide) offsetBound rawBound (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [raw] using lowEq) (by simpa [raw] using highEq)
  have sumEq : raw.toBitVec = base.toBitVec + offset.toBitVec := by
    simpa [Word.toBitVec, Word.value, limbBase] using sum
  constructor
  · cases indirect
    · have aligned : (w 81).val % 4 = 0 := by
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


end Airbender.UnifiedReduced.Proofs
