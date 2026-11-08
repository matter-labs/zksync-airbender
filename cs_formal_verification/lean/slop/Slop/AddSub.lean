module
public import Slop.AddSub.RowModel
public import Slop.Arithmetic.Lemmas
public import Slop.Arithmetic.Word
public import Slop.AddSub.PC
public import Slop.Constraints
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Airbender.AddSub.Proofs
open Airbender.Reference.RiscV
open Airbender.Arithmetic

private theorem carry_bits {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (∃ c : Nat, c ≤ 1 ∧ w 39 = (c : ZMod p)) ∧
    (∃ c : Nat, c ≤ 1 ∧ w 40 = (c : ZMod p)) := by
  have h39 := Verification.assertion_of_holds h ⟨25, by rw [constraint_count]; decide⟩
  have h40 := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
  op_index at h39 h40
  simp [Expression.eval, Verification.environment] at h39 h40
  constructor
  · apply Arithmetic.boolean_nat
    simpa [mul_eq_zero, sub_eq_add_neg] using h39
  · apply Arithmetic.boolean_nat
    simpa [mul_eq_zero, sub_eq_add_neg] using h40

private theorem selected_equations_row {p : Nat} [Fact p.Prime] {row : RowInput} {rd : BitVec 5}
    {output : Circuit.Output} {w : Nat → ZMod p} (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContractRow row rd w) (nonzero : rd ≠ 0) (wm : RowWordMappingRow row rd output w)
    {c d : Nat} (hc : w 39 = (c : ZMod p)) (hd : w 40 = (d : ZMod p)) :
    match row.opcode with
    | .sub =>
      (output.destination.lo : ZMod p) + row.right.lo = row.left.lo + 65536 * c ∧
      (c : ZMod p) + output.destination.hi + row.right.hi = row.left.hi + 65536 * d
    | .auipc =>
      (row.pc.lo : ZMod p) + row.immediate.lo = output.destination.lo + 65536 * c ∧
      (c : ZMod p) + row.pc.hi + row.immediate.hi = output.destination.hi + 65536 * d
    | _ =>
      (row.left.lo : ZMod p) + row.right.lo + row.immediate.lo = output.destination.lo + 65536 * c ∧
      (c : ZMod p) + row.left.hi + row.right.hi + row.immediate.hi = output.destination.hi + 65536 * d := by
  -- `simp` normalises the BitVec literal to `0#5`; the hypothesis must use the same normal form.
  have nz : rd ≠ 0#5 := nonzero
  have outLo : w 33 = (output.destination.lo : ZMod p) := by
    rw [wm.outputLo]; exact (ZMod.natCast_zmod_val _).symm
  have outHi : w 34 = (output.destination.hi : ZMod p) := by
    rw [wm.outputHi]; exact (ZMod.natCast_zmod_val _).symm
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  have s12 := dc.otherSelectors 12 (by omega) (by omega)
  have s13 := dc.otherSelectors 13 (by omega) (by omega)
  have s14 := dc.otherSelectors 14 (by omega) (by omega)
  have s15 := dc.otherSelectors 15 (by omega) (by omega)
  have s16 := dc.otherSelectors 16 (by omega) (by omega)
  op_index at lo hi
  simp [Expression.eval, Verification.environment, dc.addSelector, dc.subSelector, nz,
    s12, s13, s14, s15, s16, wm.leftLo, wm.leftHi, wm.rightLo, wm.rightHi,
    wm.immediateLo, wm.immediateHi, wm.pcLo, wm.pcHi, outLo, outHi, hc, hd] at lo hi
  cases hop : row.opcode <;> simp [hop] at lo hi ⊢ <;> constructor
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
    ⟨2, by rw [lookup_count]; decide⟩)
  have hi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by rw [lookup_count]; decide⟩)
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
  have lo := Verification.assertion_of_holds h ⟨4, by rw [constraint_count]; decide⟩
  have hi := Verification.assertion_of_holds h ⟨5, by rw [constraint_count]; decide⟩
  have flags : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0 ∧ w 14 = 0 ∧ w 15 = 0 ∧
      w 16 = 0 := by
    repeat' apply And.intro
    all_goals apply others <;> omega
  op_index at lo hi
  simp [Expression.eval, Verification.environment,
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

/-- Shared limb calculation for the standard arithmetic clauses over `(row, rd)`, independent
    of artifact placement and selector gates. Callers supply the instruction meaning. -/
theorem result_of_limbs_row {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {row : RowInput} {rd : BitVec 5} {output : Circuit.Output} {c d : Nat}
    (nonzero : rd ≠ 0) (preprocessing : PreprocessingRow row rd)
    (bounds : InputBounds row) (pcBounds : row.pc.Bounded)
    (resultBounds : output.destination.Bounded) (cb : c ≤ 1) (db : d ≤ 1)
    (eqs : match row.opcode with
      | .sub =>
        (output.destination.lo : ZMod p) + row.right.lo = row.left.lo + 65536 * c ∧
        (c : ZMod p) + output.destination.hi + row.right.hi = row.left.hi + 65536 * d
      | .auipc =>
        (row.pc.lo : ZMod p) + row.immediate.lo = output.destination.lo + 65536 * c ∧
        (c : ZMod p) + row.pc.hi + row.immediate.hi = output.destination.hi + 65536 * d
      | _ =>
        (row.left.lo : ZMod p) + row.right.lo + row.immediate.lo = output.destination.lo + 65536 * c ∧
        (c : ZMod p) + row.left.hi + row.right.hi + row.immediate.hi = output.destination.hi + 65536 * d) :
    output.destination.toBitVec = match row.opcode with
      | .add => row.left.toBitVec + row.right.toBitVec
      | .addi => row.left.toBitVec + row.immediate.toBitVec
      | .sub => row.left.toBitVec - row.right.toBitVec
      | .lui => row.immediate.toBitVec
      | .auipc => row.pc.toBitVec + row.immediate.toBitVec := by
  have nz : rd ≠ 0#5 := nonzero
  cases hop : row.opcode <;> simp only [hop] at eqs ⊢
  · have pre := preprocessing
    simp only [PreprocessingRow, nonzero, ite_false, hop] at pre
    simpa [pre, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) eqs.1 eqs.2)
  · have pre := preprocessing
    simp only [PreprocessingRow, nonzero, ite_false, hop] at pre
    simpa [pre, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) eqs.1 eqs.2)
  · exact Word.sub_of_limbs (by omega) bounds.leftBound bounds.rightBound
      resultBounds cb db eqs.1 eqs.2
  · have pre := preprocessing
    simp only [PreprocessingRow, nonzero, ite_false, hop] at pre
    simpa [pre.1, pre.2, Word.toBitVec, Word.value] using
      (Word.add_of_limbs hp bounds.leftBound bounds.rightBound bounds.immediateBound
        resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) eqs.1 eqs.2)
  · simpa [Word.toBitVec, Word.value] using
      (Word.add_of_limbs (right := ⟨0, 0⟩) hp pcBounds ⟨by decide, by decide⟩
        bounds.immediateBound resultBounds (Nat.le_trans cb (by decide)) (Nat.le_trans db (by decide)) (by simpa using eqs.1) (by simpa using eqs.2))

/-- A calculation lemma over `(row, rd)`, derived from the imported constraints, not an ISA spec. -/
theorem result_word_row {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) {row : RowInput} {rd : BitVec 5} {output : Circuit.Output} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (dc : DecoderContractRow row rd w) (nonzero : rd ≠ 0) (bounds : InputBounds row) (pcBounds : row.pc.Bounded)
    (mapping : RowWordMappingRow row rd output w) :
    output.destination.toBitVec = match row.opcode with
      | .add => row.left.toBitVec + row.right.toBitVec
      | .addi => row.left.toBitVec + row.immediate.toBitVec
      | .sub => row.left.toBitVec - row.right.toBitVec
      | .lui => row.immediate.toBitVec
      | .auipc => row.pc.toBitVec + row.immediate.toBitVec := by
  obtain ⟨⟨c, cb, hc⟩, ⟨d, db, hd⟩⟩ := carry_bits h
  have written := written_limb_bounds h
  have resultBounds : output.destination.Bounded :=
    ⟨mapping.outputLo ▸ written.1, mapping.outputHi ▸ written.2⟩
  exact result_of_limbs_row hp nonzero dc.preprocessing bounds pcBounds
    resultBounds cb db (selected_equations_row h dc nonzero mapping hc hd)

end Airbender.AddSub.Proofs
