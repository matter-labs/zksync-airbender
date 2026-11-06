import Airbender.Proofs.ReducedMachine.NativeComparisonOperand
import Airbender.Proofs.ReducedMachine.NativeComparisonResult

namespace Airbender.ReducedMachine.NativeComparisonResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original immediate/routing bounds the selected operand after initialized
    history supplies the actual readonly input range. -/
theorem operand_bound {w : Nat → ZMod mersenne31Modulus} {entry : ComparisonProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : comparisonDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (right : (registerOperandWord w).Bounded) :
    (operandWord w).Bounded := by
  rw [NativeComparisonOperandProofs.entry_selected_operand native fields query]
  cases choice : entry.data.family.useRegister
  · simp only [Bool.false_eq_true,if_false]
    exact (NativeComparisonDecoderProofs.field_bounds fields).1
  · simp only [if_true]
    exact right

/-- Full canonical comparison and original decoded x0 mask. The two readonly
    input ranges are internal and must be discharged by initialized history. -/
theorem decoded_result {w : Nat → ZMod mersenne31Modulus} {entry : ComparisonProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : comparisonDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (left : (sourceWord w).Bounded)
    (right : (registerOperandWord w).Bounded) :
    candidateWord w = Word.ofBitVec (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec) ∧
    writtenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
      (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec) := by
  have decoded := NativeComparisonDecoderProofs.decoded_fields fields query
  have tag : w 11 = if entry.data.family.signed then 2 else 3 := by
    simpa [ComparisonMode.tag] using decoded.funct3
  have selectedBound := operand_bound native fields query right
  have value := resolution native entry.data.family.useRegister entry.data.family.signed decoded.mask tag left selectedBound
  let answer : Nat := if entry.data.family.signed then
    (if (sourceWord w).toBitVec.toInt < (operandWord w).toBitVec.toInt then 1 else 0)
    else (if (sourceWord w).value < (operandWord w).value then 1 else 0)
  have bound : answer < mersenne31Modulus := by dsimp [answer]; split_ifs <;> decide
  have candidate := NativeComparisonFieldProofs.candidate native entry.data.family.useRegister decoded.mask
  have canonical : candidateWord w = ⟨answer,0⟩ := by
    change Word.mk (w 116).val (w 117).val = _
    rw [candidate.1,candidate.2,value,ZMod.val_natCast_of_lt bound]
    rfl
  have result : candidateWord w = Word.ofBitVec
      (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec) := by
    rw [canonical]
    simp only [ComparisonMode.result,Word.toBitVec_toNat left,Word.toBitVec_toNat selectedBound]
    dsimp [answer]
    split_ifs <;> decide +kernel
  refine ⟨result,?_⟩
  have actual := (NativeComparisonFieldProofs.write native entry.data.family.useRegister decoded.mask).2
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  by_cases zero : entry.data.rd = 0
  · rw [if_pos zero]
    have flag : rdZeroFlag w = 1 := by rw [decoded.zero,if_pos zero]
    simp [flag,arithmeticCandidate] at low high
    simp [writtenWord,low,high]
  · rw [if_neg zero]
    have flag : rdZeroFlag w = 0 := by rw [decoded.zero,if_neg zero]
    simp [flag,arithmeticCandidate] at low high
    simpa only [writtenWord,low,high,candidateWord] using result

end Airbender.ReducedMachine.NativeComparisonResultProofs
