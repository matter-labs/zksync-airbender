import Airbender.Proofs.AddSub.RowModel
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.PC
import Airbender.Proofs.AddSub.PC
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

private theorem selected_equations {p : Nat} [Fact p.Prime] {input : Sail.Input}
    {output : Sail.Output} {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContract input w) (nonzero : input.rd ≠ Sail.zeroRegister) (wm : RowWordMapping input output w)
    {c d : Nat} (hc : w 39 = (c : ZMod p)) (hd : w 40 = (d : ZMod p)) :
    match input.row.opcode with
    | .sub =>
      (output.destination.lo : ZMod p) + input.row.right.lo = input.row.left.lo + 65536 * c ∧
      (c : ZMod p) + output.destination.hi + input.row.right.hi = input.row.left.hi + 65536 * d
    | .auipc =>
      (input.row.pc.lo : ZMod p) + input.row.immediate.lo = output.destination.lo + 65536 * c ∧
      (c : ZMod p) + input.row.pc.hi + input.row.immediate.hi = output.destination.hi + 65536 * d
    | _ =>
      (input.row.left.lo : ZMod p) + input.row.right.lo + input.row.immediate.lo = output.destination.lo + 65536 * c ∧
      (c : ZMod p) + input.row.left.hi + input.row.right.hi + input.row.immediate.hi = output.destination.hi + 65536 * d := by
  have outLo : w 33 = (output.destination.lo : ZMod p) := by
    rw [wm.outputLo]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 34 = (output.destination.hi : ZMod p) := by
    rw [wm.outputHi]; exact (ZMod.natCast_zmod_val _).symm
  have lo := Verification.assertion_of_holds h ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  have hi := Verification.assertion_of_holds h ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have s12 := dc.otherSelectors 12 (by omega) (by omega)
  have s13 := dc.otherSelectors 13 (by omega) (by omega)
  have s14 := dc.otherSelectors 14 (by omega) (by omega)
  have s15 := dc.otherSelectors 15 (by omega) (by omega)
  have s16 := dc.otherSelectors 16 (by omega) (by omega)
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, dc.addSelector, dc.subSelector, nonzero,
    s12, s13, s14, s15, s16, wm.leftLo, wm.leftHi, wm.rightLo, wm.rightHi,
    wm.immediateLo, wm.immediateHi, wm.pcLo, wm.pcHi, outLo, outHi, hc, hd] at lo hi
  cases hop : input.row.opcode <;> simp [hop] at lo hi ⊢ <;> constructor
  all_goals
    apply sub_eq_zero.mp
    solve
      | convert lo using 1; ring
      | convert hi using 1; ring

/-- Both written limbs are bounded by the imported output range queries. -/
theorem written_limb_bounds {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 33).val < limbBase ∧ (w 34).val < limbBase := by
  have lo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have hi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at lo hi
  exact ⟨lo, hi⟩

/-- The native zero-operand ADD preprocessing writes the zero word. This
    calculation uses the same imported equations, carry bits and output ranges. -/
theorem zero_operands_result {p : Nat} [Fact p.Prime] (hp : 196608 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 10 = 1) (others : ∀ k, 11 ≤ k → k ≤ 16 → w k = 0)
    (operands : w 25 = 0 ∧ w 26 = 0 ∧ w 29 = 0 ∧ w 30 = 0 ∧ w 8 = 0 ∧ w 9 = 0) :
    (Word.mk (w 33).val (w 34).val).toBitVec = 0 := by
  obtain ⟨⟨c, cb, hc⟩, ⟨d, db, hd⟩⟩ := carry_bits h
  obtain ⟨leftLo, leftHi, rightLo, rightHi, immediateLo, immediateHi⟩ := operands
  have lo := Verification.assertion_of_holds h ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  have hi := Verification.assertion_of_holds h ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have flags : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧
      w 16 = 0 := by
    repeat' apply And.intro
    all_goals apply others <;> omega
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected, flags.1, flags.2.1, flags.2.2.1, flags.2.2.2.1, flags.2.2.2.2.1,
    flags.2.2.2.2.2,
    leftLo, leftHi, rightLo, rightHi, immediateLo, immediateHi, hc, hd] at lo hi
  have low : (0 : ZMod p) + 0 + 0 = (w 33).val + 65536 * c := by
    rw [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    convert lo using 1; ring
  have high : (c : ZMod p) + 0 + 0 + 0 = (w 34).val + 65536 * d := by
    rw [ZMod.natCast_zmod_val]
    apply sub_eq_zero.mp
    convert hi using 1; ring
  have zeroBound : (Word.mk 0 0).Bounded := ⟨by decide, by decide⟩
  simpa [Word.toBitVec, Word.value] using Word.add_of_limbs
    (left := ⟨0, 0⟩) (right := ⟨0, 0⟩) (immediate := ⟨0, 0⟩)
    (output := ⟨(w 33).val, (w 34).val⟩) hp zeroBound zeroBound zeroBound
    (written_limb_bounds h) (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide))
    (by simpa only [Nat.cast_zero] using low) (by simpa only [Nat.cast_zero] using high)

/-- The result's limb bounds follow from the two imported output range queries. -/
theorem output_bounds {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {input : Sail.Input} {output : Sail.Output}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : RowWordMapping input output w) : output.destination.Bounded := by
  have bounds := written_limb_bounds h
  exact ⟨mapping.outputLo ▸ bounds.1, mapping.outputHi ▸ bounds.2⟩

/-- Shared limb calculation for the standard arithmetic clauses, independent
    of artifact placement and selector gates. Sail supplies the instruction meaning. -/
theorem result_of_limbs {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {input : Sail.Input} {output : Sail.Output} {c d : Nat}
    (nonzero : input.rd ≠ Sail.zeroRegister) (preprocessing : Preprocessing input)
    (bounds : InputBounds input.row) (pcBounds : input.row.pc.Bounded)
    (resultBounds : output.destination.Bounded) (cb : c ≤ 1) (db : d ≤ 1)
    (eqs : match input.row.opcode with
      | .sub =>
        (output.destination.lo : ZMod p) + input.row.right.lo = input.row.left.lo + 65536 * c ∧
        (c : ZMod p) + output.destination.hi + input.row.right.hi = input.row.left.hi + 65536 * d
      | .auipc =>
        (input.row.pc.lo : ZMod p) + input.row.immediate.lo = output.destination.lo + 65536 * c ∧
        (c : ZMod p) + input.row.pc.hi + input.row.immediate.hi = output.destination.hi + 65536 * d
      | _ =>
        (input.row.left.lo : ZMod p) + input.row.right.lo + input.row.immediate.lo = output.destination.lo + 65536 * c ∧
        (c : ZMod p) + input.row.left.hi + input.row.right.hi + input.row.immediate.hi = output.destination.hi + 65536 * d) :
    output.destination.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec := by
  cases hop : input.row.opcode <;> simp only [hop] at eqs ⊢
  · have pre := preprocessing
    simp only [Preprocessing, nonzero, if_false, hop] at pre
    simpa [pre, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) eqs.1 eqs.2)
  · have pre := preprocessing
    simp only [Preprocessing, nonzero, if_false, hop] at pre
    simpa [pre, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) eqs.1 eqs.2)
  · exact Word.sub_of_limbs (by omega) bounds.leftBound bounds.rightBound
      resultBounds cb db eqs.1 eqs.2
  · have pre := preprocessing
    simp only [Preprocessing, nonzero, if_false, hop] at pre
    simpa [pre.1, pre.2, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) eqs.1 eqs.2)
  · simpa [Word.toBitVec, Word.value] using
      (Word.add_of_limbs (right := ⟨0, 0⟩) hp pcBounds ⟨by decide, by decide⟩
        bounds.immediateBound resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) (by simpa using eqs.1) (by simpa using eqs.2))


/-- A calculation lemma derived from the imported constraints, not an ISA spec. -/
theorem result_word {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) {input : Sail.Input} {output : Sail.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContract input w) (nonzero : input.rd ≠ Sail.zeroRegister) (bounds : InputBounds input.row) (pcBounds : input.row.pc.Bounded)
    (mapping : RowWordMapping input output w) :
    output.destination.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec := by
  obtain ⟨⟨c, cb, hc⟩, ⟨d, db, hd⟩⟩ := carry_bits h
  exact result_of_limbs hp nonzero dc.preprocessing bounds pcBounds
    (output_bounds h mapping) cb db (selected_equations h dc nonzero mapping hc hd)

/-- Combined destination/PC soundness for the decoded four-byte Sail path. -/
theorem soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (rowCircuitModel (p := p)).SoundnessUnder RowInterfaces Sail.spec := by
  rintro input output w ⟨assumptions, constraints, mapping⟩
  have pc := pc_successor hp inverse constraints
    (PCMapping.mk mapping.pcLo mapping.pcHi mapping.finalPCLo mapping.finalPCHi)
    assumptions.initialPCBounds
  apply Sail.step_of_destination assumptions.registers pc.2.2
  intro state contract
  by_cases hz : input.rd = Sail.zeroRegister
  · exact Sail.spec_zero_write contract hz
  · apply Sail.spec_of_result contract hz
    have result := result_word hp constraints assumptions.decoder hz (assumptions.ranges hz)
      assumptions.initialPCBounds mapping
    exact result

end Airbender.AddSub.Proofs
