import Airbender.Review.AddSub.Model
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.RiscV
import Airbender.Proofs.Constraints

namespace Airbender.AddSub.Proofs
open Airbender.Reference.RiscV
open Airbender.Arithmetic

private theorem carry_bits {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (∃ c : Nat, c ≤ 1 ∧ w 39 = (c : ZMod p)) ∧
    (∃ c : Nat, c ≤ 1 ∧ w 40 = (c : ZMod p)) := by
  have h39 := Verification.assertion_of_holds h ⟨25, by simp [importedConstraints, FlatOperation.constraints]⟩
  have h40 := Verification.assertion_of_holds h ⟨26, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] at h39 h40
  constructor
  · apply Arithmetic.boolean_nat
    simpa [mul_eq_zero, sub_eq_add_neg] using h39
  · apply Arithmetic.boolean_nat
    simpa [mul_eq_zero, sub_eq_add_neg] using h40

private theorem selected_equations {p : Nat} [Fact p.Prime] {input : RowInput}
    {output : Word} {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContract input w) (wm : WordMapping input output w)
    {c d : Nat} (hc : w 39 = (c : ZMod p)) (hd : w 40 = (d : ZMod p)) :
    match input.opcode with
    | .sub =>
      (output.lo : ZMod p) + input.right.lo = input.left.lo + 65536 * c ∧
      (c : ZMod p) + output.hi + input.right.hi = input.left.hi + 65536 * d
    | .auipc =>
      (input.pc.lo : ZMod p) + input.immediate.lo = output.lo + 65536 * c ∧
      (c : ZMod p) + input.pc.hi + input.immediate.hi = output.hi + 65536 * d
    | _ =>
      (input.left.lo : ZMod p) + input.right.lo + input.immediate.lo = output.lo + 65536 * c ∧
      (c : ZMod p) + input.left.hi + input.right.hi + input.immediate.hi = output.hi + 65536 * d := by
  have outLo : w 33 = (output.lo : ZMod p) := by
    rw [wm.outputLo]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 34 = (output.hi : ZMod p) := by
    rw [wm.outputHi]; exact (ZMod.natCast_zmod_val _).symm
  have lo := Verification.assertion_of_holds h ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  have hi := Verification.assertion_of_holds h ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have s12 := dc.otherSelectors 12 (by omega) (by omega)
  have s13 := dc.otherSelectors 13 (by omega) (by omega)
  have s14 := dc.otherSelectors 14 (by omega) (by omega)
  have s15 := dc.otherSelectors 15 (by omega) (by omega)
  have s16 := dc.otherSelectors 16 (by omega) (by omega)
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, dc.addSelector, dc.subSelector,
    s12, s13, s14, s15, s16, wm.leftLo, wm.leftHi, wm.rightLo, wm.rightHi,
    wm.immediateLo, wm.immediateHi, wm.pcLo, wm.pcHi, outLo, outHi, hc, hd] at lo hi
  cases hop : input.opcode <;> simp [hop] at lo hi ⊢ <;> constructor
  all_goals
    apply sub_eq_zero.mp
    solve
      | convert lo using 1; ring
      | convert hi using 1; ring

/-- The result's limb bounds follow from the two imported output range queries. -/
theorem output_bounds {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {input : RowInput} {output : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : WordMapping input output w) : output.Bounded := by
  have lo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have hi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at lo hi
  exact ⟨mapping.outputLo ▸ lo, mapping.outputHi ▸ hi⟩

/-- A calculation lemma derived from the imported constraints, not an ISA spec. -/
theorem result_word {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) {input : RowInput} {output : Word} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContract input w) (bounds : InputBounds input)
    (mapping : WordMapping input output w) :
    output.toBitVec = match input.opcode with
      | .add => input.left.toBitVec + input.right.toBitVec
      | .addi => input.left.toBitVec + input.immediate.toBitVec
      | .sub => input.left.toBitVec - input.right.toBitVec
      | .lui => input.immediate.toBitVec
      | .auipc => input.pc.toBitVec + input.immediate.toBitVec := by
  obtain ⟨⟨c, cb, hc⟩, ⟨d, db, hd⟩⟩ := carry_bits h
  have eqs := selected_equations h dc mapping hc hd
  have resultBounds := output_bounds h mapping
  cases hop : input.opcode <;> simp only [hop] at eqs ⊢
  · have pre := dc.preprocessing
    simp only [hop] at pre
    simpa [pre, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds cb db eqs.1 eqs.2)
  · have pre := dc.preprocessing
    simp only [hop] at pre
    simpa [pre, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds cb db eqs.1 eqs.2)
  · exact Word.sub_of_limbs (by omega) bounds.leftBound bounds.rightBound
      resultBounds cb db eqs.1 eqs.2
  · have pre := dc.preprocessing
    simp only [hop] at pre
    simpa [pre.1, pre.2, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds cb db eqs.1 eqs.2)
  · simpa [Word.toBitVec, Word.value] using
      (Word.add_of_limbs (right := ⟨0, 0⟩) hp (bounds.pcBound hop) ⟨by decide, by decide⟩
        bounds.immediateBound resultBounds cb db (by simpa using eqs.1) (by simpa using eqs.2))

/-- Any satisfying assignment with the stated interfaces agrees with Sail's execution.
    This covers standard arithmetic destination writes, not a full architectural step. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions Sail.spec := by
  rintro input output w ⟨assumptions, constraints, mapping⟩
  exact Sail.spec_of_result assumptions.registers
    (result_word hp constraints assumptions.decoder assumptions.ranges mapping)

end Airbender.AddSub.Proofs
