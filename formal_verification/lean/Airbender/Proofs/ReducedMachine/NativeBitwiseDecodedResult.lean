import Airbender.Proofs.ReducedMachine.NativeBitwiseDecoder
import Airbender.Proofs.ReducedMachine.NativeBitwiseResult

namespace Airbender.ReducedMachine.NativeBitwiseResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original decoding supplies the actual native mask/tag and rd/x0 binding.
    All numerical source/selected/candidate ranges are derived by byte queries. -/
theorem decoded_result {w : Nat → ZMod mersenne31Modulus} {entry : BitwiseProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : bitwiseDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    (sourceWord w).Bounded ∧ (operandWord w).Bounded ∧
    candidateWord w = Word.ofBitVec (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec) ∧
    writtenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
      (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec) := by
  have decoded := NativeBitwiseDecoderProofs.decoded_fields fields query
  obtain ⟨source,operand,bounds,bits⟩ := candidate_result holds entry.data.family.kind
    entry.data.family.useRegister decoded.mask decoded.funct3
  have result : candidateWord w = Word.ofBitVec
      (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec) := by
    apply Word.eq_of_value bounds (Word.ofBitVec_bound _)
    rw [Word.ofBitVec_value,BitwiseMode.result,← bits,Word.toBitVec_toNat bounds]
  refine ⟨source,operand,result,?_⟩
  have actual := (NativeBitwiseFieldProofs.write holds entry.data.family.useRegister decoded.mask).2
  have first := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have second := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  by_cases zero : entry.data.rd = 0
  · rw [if_pos zero]
    have flag : rdZeroFlag w = 1 := by rw [decoded.zero,if_pos zero]
    simp [flag,arithmeticCandidate] at first second
    simp [writtenWord,first,second]
  · rw [if_neg zero]
    have flag : rdZeroFlag w = 0 := by rw [decoded.zero,if_neg zero]
    simp [flag,arithmeticCandidate] at first second
    simpa only [writtenWord,first,second,candidateWord] using result

end Airbender.ReducedMachine.NativeBitwiseResultProofs
