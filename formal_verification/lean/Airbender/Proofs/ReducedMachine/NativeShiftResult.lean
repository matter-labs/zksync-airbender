import Airbender.Proofs.ReducedMachine.NativeShiftAssembly
import Airbender.Proofs.ReducedMachine.NativeShiftPreservation

namespace Airbender.ReducedMachine.NativeShiftResultProofs
open Native Arithmetic Verification NativeShiftNaturalProofs NativeShiftWordProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact canonical native candidate; the source bound is internal and is
    discharged by initialized history at the public trace entry point. -/
theorem candidate_result {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mode : ShiftMode) (useRegister : Bool)
    (mask : w 12 = (mode.mask useRegister : ZMod mersenne31Modulus))
    (source : (sourceWord w).Bounded) :
    candidateWord w = Word.ofBitVec (mode.result (sourceWord w).toBitVec
      ((operandWord w).toBitVec.extractLsb' 0 5).toNat) := by
  have amount := NativeShiftRoutingProofs.amount holds mode useRegister mask
  have values := NativeShiftBoundedProofs.candidate_values holds mode useRegister mask source
  have bounds := NativeShiftBoundedProofs.candidate_bounds holds mode useRegister mask source
  have bits : (candidateWord w).toBitVec =
      mode.result (sourceWord w).toBitVec (shiftAmount w).val := by
    change (Word.toBitVec ⟨(w 116).val,(w 117).val⟩) = _
    rw [values.1,values.2]
    exact assembled_result mode _ _ ⟨_,amount.2.2.1⟩ source.1 source.2
  rw [word_shift_amount]
  change candidateWord w = Word.ofBitVec (mode.result (sourceWord w).toBitVec ((source2 w)[0].val % 32))
  rw [← amount.2.1]
  apply Word.eq_of_value bounds (Word.ofBitVec_bound _)
  rw [Word.ofBitVec_value,← bits,Word.toBitVec_toNat bounds]

/-- Actual original-rd/x0 masked native write equals the complete RV32 result. -/
theorem decoded_result {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded) :
    candidateWord w = Word.ofBitVec (entry.data.family.result (sourceWord w).toBitVec
      ((operandWord w).toBitVec.extractLsb' 0 5).toNat) ∧
    writtenWord w = if entry.data.rd = 0 then ⟨0,0⟩ else
      Word.ofBitVec (entry.data.family.result (sourceWord w).toBitVec
        ((operandWord w).toBitVec.extractLsb' 0 5).toNat) := by
  have decoded := NativeShiftDecoderProofs.decoded_fields fields query
  obtain ⟨useRegister,mask⟩ := decoded.mask
  have result := candidate_result holds entry.data.family useRegister mask source
  refine ⟨result,?_⟩
  have candidate := NativeShiftWriteProofs.candidate holds entry.data.family useRegister mask
  have write := NativeShiftWriteProofs.write holds entry.data.family useRegister mask
  have actual : rdWrite w = (#v[w 116,w 117]).map (fun value => (1 - rdZeroFlag w) * value) :=
    write.trans (congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 =>
      v.map (fun value => (1 - rdZeroFlag w) * value)) candidate).symm
  have first := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have second := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  by_cases zero : entry.data.rd = 0
  · rw [if_pos zero]
    have flag : rdZeroFlag w = 1 := by rw [decoded.zero,if_pos zero]
    simp [flag] at first second
    simp [writtenWord,first,second]
  · rw [if_neg zero]
    have flag : rdZeroFlag w = 0 := by rw [decoded.zero,if_neg zero]
    simp [flag] at first second
    simpa only [writtenWord,first,second,candidateWord] using result

end Airbender.ReducedMachine.NativeShiftResultProofs
