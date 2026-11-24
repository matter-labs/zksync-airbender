module
public import Proven.Blake2Round.Mask.WitnessData

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option maxRecDepth 32768

theorem zero_reads : ∀ i : Fin 43, (readWord zeroAssignment i).Bounded := by
  simp only [Word.Bounded]
  decide +kernel

/-- Every native round selector of the witness is false. -/
theorem zero_rounds (round : Fin 10) : (inputOf zeroAssignment).rounds round = false := by
  change decide (zeroAssignment (142 + round.val) = 1) = false
  have lower : 142 ≤ 142 + round.val := by omega
  have upper : 142 + round.val < 152 := by have := round.isLt; omega
  have zero : zeroAssignment (142 + round.val) = 0 := by
    unfold zeroAssignment
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  rw [zero]
  simp

end Airbender.Blake2Round.Mask.Proofs
