import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.JumpBranchSlt.PC

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- JAL and JALR share the saved PC+4 word and destination mask. The mask's
    meaning as rd=x0 is a decoder obligation; its Booleanity is imported. -/
theorem jump_link {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {w : Nat → ZMod p} {initial : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 + w 12 = 1) (other : w 13 = 0 ∧ w 14 = 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val)
    (initialLoBound : initial.lo < limbBase) :
    (⟨(w 30).val, (w 31).val⟩ : Word).toBitVec =
      (if w 15 = 1 then 0 else initial.toBitVec + 4) ∧
    (⟨(w 30).val, (w 31).val⟩ : Word).Bounded := by
  have bounds := local_ranges h
  obtain ⟨c, b, cb, bb, hc, hb⟩ := arithmetic_carries h
  have low := Verification.assertion_of_holds h
    ⟨1, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.1, other.2, hc, hb] at low high
  have initialLo : w 0 = (initial.lo : ZMod p) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have initialHi : w 1 = (initial.hi : ZMod p) := by
    rw [mapping.2]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (initial.lo : ZMod p) + 4 = (w 34).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [← initialLo]
    linear_combination low - (w 0 + 4 - w 34 - 65536 * c) * selected
  have highEq : (c : ZMod p) + initial.hi = (w 35).val + 65536 * b := by
    simp only [ZMod.natCast_zmod_val]
    rw [← initialHi]
    linear_combination high - ((c : ZMod p) + w 1 - w 35 - 65536 * b) * selected
  have link := Word.add_of_limbs (by omega : 196608 < p)
    (left := initial) (right := ⟨0, 0⟩) (immediate := ⟨4, 0⟩)
    (output := ⟨(w 34).val, (w 35).val⟩)
    ⟨initialLoBound, mapping.2 ▸ bounds.2.2.1⟩ (by constructor <;> decide)
    (by constructor <;> decide) ⟨bounds.1, bounds.2.1⟩ (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa using lowEq) (by simpa using highEq)
  have lo := Verification.assertion_of_holds h
    ⟨8, by simp [importedConstraints, FlatOperation.constraints]⟩
  have hi := Verification.assertion_of_holds h
    ⟨9, by simp [importedConstraints, FlatOperation.constraints]⟩
  have maskLo := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have maskHi := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.1, selected] at lo hi
  have selectedLo : w 47 = w 34 := by linear_combination -lo
  have selectedHi : w 48 = w 35 := by linear_combination -hi
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selectedLo, selectedHi] at maskLo maskHi
  rcases (local_flags h).2 ⟨4, by decide⟩ with zero | one
  · change w 15 = 0 at zero
    have destLo : w 30 = w 34 := by rw [zero] at maskLo; linear_combination -maskLo
    have destHi : w 31 = w 35 := by rw [zero] at maskHi; linear_combination -maskHi
    rw [destLo, destHi]
    exact ⟨by simpa [zero, Word.toBitVec, Word.value, limbBase] using link,
      bounds.1, bounds.2.1⟩
  · change w 15 = 1 at one
    have destLo : w 30 = 0 := by rw [one] at maskLo; linear_combination -maskLo
    have destHi : w 31 = 0 := by rw [one] at maskHi; linear_combination -maskHi
    simp [destLo, destHi, one, Word.toBitVec, Word.value, Word.Bounded, limbBase]

/-- Local JAL/JALR targets: `base` is PC for JAL, rs1 for JALR. The bit-1
    assertion enforces four-byte alignment; JALR may clear an odd sum's bit 0.
    Bounds, direct-offset parity and selector identity remain interfaces. -/
theorem jump_pc {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NativeRomCapacity p)
    {w : Nat → ZMod p} {base offset final : Word} (indirect : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = (if indirect then 0 else 1) ∧ w 12 = (if indirect then 1 else 0))
    (other : w 13 = 0 ∧ w 14 = 0)
    (mapping : base.lo = (w (if indirect then 22 else 0)).val ∧
      base.hi = (w (if indirect then 23 else 1)).val ∧
      w 8 = (offset.lo : ZMod p) ∧ w 9 = (offset.hi : ZMod p) ∧
      final.lo = (w 16).val ∧ final.hi = (w 17).val)
    (baseLoBound : base.lo < limbBase)
    (sourceHiBound : indirect = true → base.hi < limbBase)
    (offsetBound : offset.Bounded)
    (directEven : indirect = false → base.lo % 2 = 0 ∧ offset.lo % 2 = 0)
    (finalHiBound : final.hi < limbBase) :
    final.toBitVec = (if indirect then (base.toBitVec + offset.toBitVec) &&& 0xfffffffe
      else base.toBitVec + offset.toBitVec) ∧ final.toBitVec.toNat % 4 = 0 := by
  have bounds := local_ranges h
  have cleanup := (lookup_values hp h).2.2.2
  obtain ⟨c, b, cb, bb, hc, hb⟩ := pc_carries h
  have branch := Verification.assertion_of_holds h
    ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.2] at branch
  have low := Verification.assertion_of_holds h
    ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨6, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.1, other.2, branch, hc, hb,
    mapping.2.2.1, mapping.2.2.2.1] at low high
  have baseLo : w (if indirect then 22 else 0) = (base.lo : ZMod p) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have baseHi : w (if indirect then 23 else 1) = (base.hi : ZMod p) := by
    rw [mapping.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have lowEq : (base.lo : ZMod p) + offset.lo = (w 36).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    cases indirect <;> dsimp at baseLo <;>
      simp [selected.1, selected.2, baseLo] at low <;>
      linear_combination low
  have highEq : (c : ZMod p) + base.hi + offset.hi = final.hi + 65536 * b := by
    have finalHi : w 17 = (final.hi : ZMod p) := by
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
  have lowNat : base.lo + offset.lo = (w 36).val + 65536 * c :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by have := offsetBound.1; unfold limbBase at *; omega)
      (by have := bounds.2.2.2; unfold limbBase at *; omega)
      (by exact_mod_cast lowEq)
  have bit1 : (w 36).val / 2 % 2 = 0 := by
    have checked := Verification.assertion_of_holds h
      ⟨7, by simp [importedConstraints, FlatOperation.constraints]⟩
    cases indirect <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, selected.1, selected.2, branch] at checked
    all_goals
      have eq : (((w 36).val / 2 % 2 : Nat) : ZMod p) = 0 := cleanup.1 ▸ checked
      have eqVal := congrArg ZMod.val eq
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
        have := Nat.mod_lt ((w 36).val / 2) (by decide : 0 < 2); omega)] at eqVal
      simpa using eqVal
  have cleaned : final.lo = (w 36).val - (w 36).val % 4 := by
    rw [mapping.2.2.2.2.1, cleanup.2, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2; unfold limbBase at this; omega)]
  have finalBound : final.Bounded :=
    ⟨by rw [cleaned]; exact lt_of_le_of_lt (Nat.sub_le _ _) bounds.2.2.2, finalHiBound⟩
  let raw : Word := ⟨(w 36).val, final.hi⟩
  have rawBound : raw.Bounded := ⟨bounds.2.2.2, finalHiBound⟩
  have sum := Word.add_of_limbs (by omega : 196608 < p)
    (left := base) (right := ⟨0, 0⟩) (immediate := offset) (output := raw)
    baseBound (by constructor <;> decide) offsetBound rawBound (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [raw] using lowEq) (by simpa [raw] using highEq)
  have sumEq : raw.toBitVec = base.toBitVec + offset.toBitVec := by
    simpa [Word.toBitVec, Word.value, limbBase] using sum
  constructor
  · cases indirect
    · have aligned : (w 36).val % 4 = 0 := by
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

end Airbender.JumpBranchSlt.Proofs
