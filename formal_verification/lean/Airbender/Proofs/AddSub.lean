import Airbender.Review.AddSub.Model
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.RiscV
import Airbender.Proofs.Determinism
import Airbender.Proofs.Constraints

namespace Airbender.AddSub.Proofs
open Airbender.Reference.RiscV
open Airbender.Arithmetic

private theorem carry_bits {F : Type} [FiniteField F] {w : Nat → F}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (∃ c : Nat, c ≤ 1 ∧ w 39 = (c : F)) ∧
    (∃ c : Nat, c ≤ 1 ∧ w 40 = (c : F)) := by
  have h39 := Verification.assertion_of_holds h ⟨25, by simp [importedConstraints, FlatOperation.constraints]⟩
  have h40 := Verification.assertion_of_holds h ⟨26, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at h39 h40
  constructor
  · apply Arithmetic.boolean_nat
    simpa [mul_eq_zero, sub_eq_add_neg] using h39
  · apply Arithmetic.boolean_nat
    simpa [mul_eq_zero, sub_eq_add_neg] using h40

private theorem selected_equations {F : Type} [FiniteField F] {input : RowInput}
    {output : Word} {w : Nat → F} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContract input w) (wm : WordMapping input output w)
    {c d : Nat} (hc : w 39 = (c : F)) (hd : w 40 = (d : F)) :
    match input.opcode with
    | .sub =>
      (output.lo : F) + input.right.lo = input.left.lo + 65536 * c ∧
      (c : F) + output.hi + input.right.hi = input.left.hi + 65536 * d
    | _ =>
      (input.left.lo : F) + input.right.lo + input.immediate.lo = output.lo + 65536 * c ∧
      (c : F) + input.left.hi + input.right.hi + input.immediate.hi = output.hi + 65536 * d := by
  have lo := Verification.assertion_of_holds h ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  have hi := Verification.assertion_of_holds h ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have s12 := dc.otherSelectors 12 (by omega) (by omega)
  have s13 := dc.otherSelectors 13 (by omega) (by omega)
  have s14 := dc.otherSelectors 14 (by omega) (by omega)
  have s15 := dc.otherSelectors 15 (by omega) (by omega)
  have s16 := dc.otherSelectors 16 (by omega) (by omega)
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, dc.addSelector, dc.subSelector,
    s12, s13, s14, s15, s16, wm.leftLo, wm.leftHi, wm.rightLo, wm.rightHi,
    wm.immediateLo, wm.immediateHi, wm.outputLo, wm.outputHi, hc, hd] at lo hi
  cases hop : input.opcode <;> simp [hop] at lo hi ⊢ <;> constructor
  all_goals
    apply sub_eq_zero.mp
    solve
      | convert lo using 1; ring
      | convert hi using 1; ring

/-- A calculation lemma derived from the imported constraints, not an ISA spec. -/
theorem result_word {F : Type} [FiniteField F] {p : Nat} [CharP F p]
    (hp : 196608 < p) {input : RowInput} {output : Word} {w : Nat → F}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContract input w) (bounds : WordBounds input output)
    (mapping : WordMapping input output w) :
    output.toBitVec = match input.opcode with
      | .add => input.left.toBitVec + input.right.toBitVec
      | .addi => input.left.toBitVec + input.immediate.toBitVec
      | .sub => input.left.toBitVec - input.right.toBitVec := by
  obtain ⟨⟨c, cb, hc⟩, ⟨d, db, hd⟩⟩ := carry_bits h
  have eqs := selected_equations h dc mapping hc hd
  obtain ⟨al, ah⟩ := bounds.leftBound
  obtain ⟨bl, bh⟩ := bounds.rightBound
  obtain ⟨ml, mh⟩ := bounds.immediateBound
  obtain ⟨rl, rh⟩ := bounds.outputBound
  unfold limbBase at al ah bl bh ml mh rl rh
  apply BitVec.eq_of_toNat_eq
  cases hop : input.opcode
  · simp only [hop] at eqs ⊢
    obtain ⟨lo, hi⟩ := eqs
    have ln : input.left.lo + input.right.lo + input.immediate.lo = output.lo + 65536 * c :=
      Arithmetic.bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast lo)
    have hn : c + input.left.hi + input.right.hi + input.immediate.hi = output.hi + 65536 * d :=
      Arithmetic.bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast hi)
    have pre := dc.preprocessing
    simp only [hop] at pre
    have hz : input.immediate.lo = 0 ∧ input.immediate.hi = 0 := by
      rw [pre]; exact ⟨rfl, rfl⟩
    simp only [BitVec.toNat_add, Word.toBitVec_toNat bounds.leftBound,
      Word.toBitVec_toNat bounds.rightBound, Word.toBitVec_toNat bounds.outputBound,
      Word.value, limbBase]
    omega
  · simp only [hop] at eqs ⊢
    obtain ⟨lo, hi⟩ := eqs
    have ln : input.left.lo + input.right.lo + input.immediate.lo = output.lo + 65536 * c :=
      Arithmetic.bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast lo)
    have hn : c + input.left.hi + input.right.hi + input.immediate.hi = output.hi + 65536 * d :=
      Arithmetic.bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast hi)
    have pre := dc.preprocessing
    simp only [hop] at pre
    have hz : input.right.lo = 0 ∧ input.right.hi = 0 := by
      rw [pre]; exact ⟨rfl, rfl⟩
    simp only [BitVec.toNat_add, Word.toBitVec_toNat bounds.leftBound,
      Word.toBitVec_toNat bounds.immediateBound, Word.toBitVec_toNat bounds.outputBound,
      Word.value, limbBase]
    omega
  · simp only [hop] at eqs ⊢
    obtain ⟨lo, hi⟩ := eqs
    have ln : output.lo + input.right.lo = input.left.lo + 65536 * c :=
      Arithmetic.bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast lo)
    have hn : c + output.hi + input.right.hi = input.left.hi + 65536 * d :=
      Arithmetic.bounded_nat_eq (F := F) (p := p) (by omega) (by omega) (by exact_mod_cast hi)
    simp only [BitVec.toNat_sub, Word.toBitVec_toNat bounds.leftBound,
      Word.toBitVec_toNat bounds.rightBound, Word.toBitVec_toNat bounds.outputBound,
      Word.value, limbBase]
    omega

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    This covers the destination write for ADD/ADDI/SUB, not a full architectural step. -/
theorem soundness {F : Type} [FiniteField F] {p : Nat} [CharP F p]
    (hp : 196608 < p) :
    (circuitModel (F := F)).SoundnessUnder InterfaceAssumptions Sail.spec := by
  rintro input output w ⟨assumptions, constraints, mapping⟩
  exact Sail.spec_of_result assumptions.registers
    (result_word hp constraints assumptions.decoder assumptions.ranges mapping)

/-- For fixed inputs, satisfying assignments have the same output word.
    Internal witness values need not be unique. -/
theorem determinism {F : Type} [FiniteField F] {p : Nat} [CharP F p]
    (hp : 196608 < p) :
    (circuitModel (F := F)).DeterminismUnder InterfaceAssumptions := by
  apply Properties.determinism_of_soundness_on
    (fun input output => output.Bounded ∧ input.rd ≠ .Regidx (0 : BitVec 5))
  · exact soundness hp
  · intro input output w h
    exact ⟨h.1.ranges.outputBound, h.1.registers.nonzeroDestination⟩
  · intro input left right hl hr sl sr
    exact Sail.spec_deterministic hl.2 hl.1 hr.1 sl sr

end Airbender.AddSub.Proofs
