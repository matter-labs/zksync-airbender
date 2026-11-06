import Airbender.Proofs.ReducedMachine.NativeArithmeticDecoder
import Airbender.Proofs.ReducedMachine.NativeArithmeticResult

namespace Airbender.ReducedMachine.NativeArithmeticResultProofs
open Native Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original public query bounds the native incoming PC. -/
theorem decoded_pc_bound {w : Nat → ZMod mersenne31Modulus} {entry : ArithmeticProgramEntry}
    (query : decoderQuery w = entry.query) : (initialPCWord w).Bounded := by
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  rw [canonical]
  exact Word.ofBitVec_bound _

/-- Original decoded immediate and native routing bound the selected operand.
    The readonly register input remains in native history on immediate forms. -/
theorem decoded_operand_bound {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ArithmeticProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (register : (⟨(w 37).val,(w 38).val⟩ : Word).Bounded) : (operandWord w).Bounded := by
  have decoded := NativeArithmeticDecoderProofs.decoded_fields fields query
  have routed := NativeArithmeticFieldProofs.source holds entry.data.family decoded.mask
  have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => (⟨v[0].val,v[1].val⟩ : Word)) routed
  have immediate : (arithmeticImmediateWord w).Bounded := by
    rw [NativeArithmeticDecoderProofs.immediate_word fields query]
    exact (NativeArithmeticDecoderProofs.field_bounds fields).1
  cases choice : entry.data.family.useRegister
  · simp only [choice,Bool.false_eq_true,if_false] at selected
    have same : operandWord w = arithmeticImmediateWord w := selected
    simpa only [same] using immediate
  · simp only [choice,if_true] at selected
    have same : operandWord w = ⟨(w 37).val,(w 38).val⟩ := selected
    simpa only [same] using register

/-- Complete numerical candidate and actual original-rd/x0 masked write.
    The two internal read bounds are discharged by initialized native history. -/
theorem decoded_result {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus} {entry : ArithmeticProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded)
    (register : (⟨(w 37).val,(w 38).val⟩ : Word).Bounded) :
    candidateWord w = Word.ofBitVec (entry.data.family.result (sourceWord w).toBitVec
      (operandWord w).toBitVec (initialPCWord w).toBitVec entry.data.immediate.toBitVec) ∧
    writtenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
      (entry.data.family.result (sourceWord w).toBitVec (operandWord w).toBitVec
        (initialPCWord w).toBitVec entry.data.immediate.toBitVec) := by
  have decoded := NativeArithmeticDecoderProofs.decoded_fields fields query
  have immediate : (arithmeticImmediateWord w).Bounded := by
    rw [NativeArithmeticDecoderProofs.immediate_word fields query]
    exact (NativeArithmeticDecoderProofs.field_bounds fields).1
  have operand := decoded_operand_bound holds fields query register
  have pc := decoded_pc_bound query
  have bounds := candidate_bounds holds entry.data.family decoded.mask (fun _ => immediate)
  have bits := candidate_result holds entry.data.family decoded.mask source operand pc immediate
  rw [NativeArithmeticDecoderProofs.immediate_word fields query] at bits
  have result : candidateWord w = Word.ofBitVec (entry.data.family.result (sourceWord w).toBitVec
      (operandWord w).toBitVec (initialPCWord w).toBitVec entry.data.immediate.toBitVec) := by
    apply Word.eq_of_value bounds (Word.ofBitVec_bound _)
    rw [Word.ofBitVec_value,← bits,Word.toBitVec_toNat bounds]
  refine ⟨result,?_⟩
  have actual := (NativeArithmeticFieldProofs.write holds entry.data.family decoded.mask).2
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

end Airbender.ReducedMachine.NativeArithmeticResultProofs
