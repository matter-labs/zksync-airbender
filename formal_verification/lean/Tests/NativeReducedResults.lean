import Airbender.Review.Trace.Families.ReducedMachine.Results

namespace Tests.NativeReducedResults
open Airbender Airbender.Arithmetic Airbender.ReducedMachine Verification
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeShiftNaturalProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Independent cross-limb and sign boundary values for all three references. -/
theorem cross_limb_results :
    (Word.toBitVec ⟨assembledLow .left 65535 32769 1,assembledHigh .left 65535 32769 1⟩) = 0x0003fffe ∧
    (Word.toBitVec ⟨assembledLow .right 65535 32769 1,assembledHigh .right 65535 32769 1⟩) = 0x4000ffff ∧
    (Word.toBitVec ⟨assembledLow .arithmetic 65535 32769 1,assembledHigh .arithmetic 65535 32769 1⟩) = 0xc000ffff := by decide +kernel

theorem last_amount_results :
    (Word.toBitVec ⟨assembledLow .left 65535 32768 31,assembledHigh .left 65535 32768 31⟩) = 0x80000000 ∧
    (Word.toBitVec ⟨assembledLow .right 65535 32768 31,assembledHigh .right 65535 32768 31⟩) = 1 ∧
    (Word.toBitVec ⟨assembledLow .arithmetic 65535 32768 31,assembledHigh .arithmetic 65535 32768 31⟩) = 0xffffffff := by decide +kernel

theorem negative_zero_shift :
    (Word.toBitVec ⟨assembledLow .arithmetic 65535 32768 0,assembledHigh .arithmetic 65535 32768 0⟩) = 0x8000ffff := by decide +kernel

/-- Positive SRA agrees with logical shift at every architectural amount. -/
theorem positive_arithmetic (amount : Fin 32) :
    ShiftMode.arithmetic.result (Word.toBitVec ⟨32769,32767⟩) amount.val =
      ShiftMode.right.result (Word.toBitVec ⟨32769,32767⟩) amount.val := by
  fin_cases amount <;> decide +kernel

/-- Original encoded SRAI funct7 bits and oversized register amounts retain
    low-five-bit selection; the high operand limb never supplies shift bits. -/
theorem operand_low_five_bits :
    ((Word.toBitVec ⟨1055,65535⟩).extractLsb' 0 5).toNat = 31 ∧
    ((Word.toBitVec ⟨32,65535⟩).extractLsb' 0 5).toNat = 0 ∧
    ((Word.toBitVec ⟨63,65535⟩).extractLsb' 0 5).toNat = 31 := by decide +kernel

/-- A negative last-bit native shift cannot masquerade as the logical result. -/
theorem corrupted_arithmetic_rejected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (ShiftMode.arithmetic.mask true : ZMod mersenne31Modulus))
    (source : sourceWord w = ⟨65535,32768⟩) (operand : operandWord w = ⟨31,0⟩)
    (wrong : (candidateWord w).toBitVec = 1) : False := by
  have bounds : (sourceWord w).Bounded := by rw [source]; norm_num [Word.Bounded,limbBase]
  have result := NativeShiftResultProofs.candidate_result holds .arithmetic true mask bounds
  have value := congrArg Word.toBitVec result
  rw [Word.ofBitVec_roundtrip,source,operand,wrong] at value
  have distinct : (1 : BitVec 32) ≠ ShiftMode.arithmetic.result (Word.toBitVec ⟨65535,32768⟩)
      ((Word.toBitVec ⟨31,0⟩).extractLsb' 0 5).toNat := by decide +kernel
  exact distinct value

/-- Discarding the destination retains the actual native numerical candidate. -/
theorem discarded_result_retained {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded)
    (discarded : entry.data.rd = 0) :
    writtenWord w = ⟨0,0⟩ ∧ candidateWord w = Word.ofBitVec
      (entry.data.family.result (sourceWord w).toBitVec
        ((operandWord w).toBitVec.extractLsb' 0 5).toNat) := by
  have result := NativeShiftResultProofs.decoded_result holds fields query source
  exact ⟨by simpa only [if_pos discarded] using result.2,result.1⟩

/-- The public initialized claim derives its source range. A claimed all-zero
    result for a selected nonzero destination must therefore match its RV32 word. -/
theorem initialized_zero_write {trace : Trace.Data mersenne31Modulus Trace.NativeReducedFamily}
    {setup : Trace.SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {count logCapacity : Nat}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (inputs : Trace.ImageBoundary (fixedData trace) before cells) (accepted : Trace.Accepted (fixedData trace))
    (decoded : ShiftDecodedTrace (fixedData trace) setup)
    (row : Trace.Row mersenne31Modulus Trace.NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    (zero : writtenWord row.assignment = ⟨0,0⟩) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧
      row.decoderQuery = entry.query ∧
      (entry.data.rd = 0 ∨ entry.data.family.result (sourceWord row.assignment).toBitVec
        ((operandWord row.assignment).toBitVec.extractLsb' 0 5).toNat = 0) := by
  obtain ⟨entry,found,source,query,_,_,write⟩ := public_shift_results image inputs accepted decoded row present
  refine ⟨entry,found,source,query,?_⟩
  by_cases discarded : entry.data.rd = 0
  · exact Or.inl discarded
  · right
    rw [if_neg discarded,zero] at write
    have bits := congrArg Word.toBitVec write
    rw [Word.ofBitVec_roundtrip] at bits
    exact bits.symm

end Tests.NativeReducedResults
