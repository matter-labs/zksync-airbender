import Airbender.Review.Circuits.AddSub.Model
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.AddSub.Proofs
open Reference.RiscV Arithmetic

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


end Airbender.AddSub.Proofs
