import Airbender.Proofs.ReducedMachine.NativeShiftClauseReference
import Airbender.Proofs.ReducedMachine.NativeShiftOperand
import Airbender.Proofs.ReducedMachine.NativeShiftResult
import Airbender.Review.Helpers.Memory.ReducedMachine

namespace Airbender.ReducedMachine.NativeShiftClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original decoding, actual selected-operand routing, numerical native results
    and original GPR transfers execute the retained original clause into the
    same state. The source range is internal and discharged by public history. -/
theorem native_clause {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (sourceWord w).Bounded)
    {before after : State}
    (transfer : ShiftRegisterTransfer (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily)
      entry before after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run clause before = .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have result := (NativeShiftResultProofs.decoded_result native fields query source).2
  have leftRead := transfer.1 ⟨0,by decide⟩
  have rightRead := transfer.1 ⟨1,by decide⟩
  have written := transfer.2
  simp only [importedConstraintsMemoryPorts,MemoryPort.readCode,MemoryPort.writeCode,
    WordColumns.code,WordColumns.evaluate,memoryWord,Nat.unpair_pair] at leftRead rightRead written
  have leftActual : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs1)) before =
      .ok (sourceWord w).toBitVec before := by
    simpa [sourceWord,source1,importedConstraintsMemoryPorts,WordColumns.evaluate,
      Word.toBitVec,Word.value,pairCode] using leftRead
  have rightActual : run (SailRV32.Functions.rX_bits (.Regidx entry.data.rs2)) before =
      .ok (registerOperandWord w).toBitVec before := by
    simpa [registerOperandWord,importedConstraintsMemoryPorts,WordColumns.evaluate,
      Word.toBitVec,Word.value,pairCode] using rightRead
  have writeActual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (writtenWord w).toBitVec) before = .ok () after := by
    simpa [writtenWord,rdWrite,rdPort,importedConstraintsMemoryPorts,WordColumns.evaluate,
      Word.toBitVec,Word.value,pairCode] using written
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd)
      (entry.data.family.result (sourceWord w).toBitVec ((operandWord w).toBitVec.extractLsb' 0 5).toNat))
      before = .ok () after := by
    by_cases zero : entry.data.rd = 0
    · rw [zero] at writeActual ⊢
      change run (SailRV32.Functions.wX_bits zeroRegister _) before = _ at writeActual ⊢
      rw [write_zero] at writeActual ⊢
      exact writeActual
    · rw [result,if_neg zero,Word.ofBitVec_roundtrip] at writeActual
      exact writeActual
  exact decoded_clause_of_reads fields _ _ _ leftActual rightActual
    (NativeShiftOperandProofs.entry_selected_operand native fields query) actual

end Airbender.ReducedMachine.NativeShiftClauseProofs
