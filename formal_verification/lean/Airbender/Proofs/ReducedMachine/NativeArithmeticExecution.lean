import Airbender.Proofs.ReducedMachine.NativeArithmeticClause
import Airbender.Proofs.ReducedMachine.NativeArithmeticPC
import Airbender.Proofs.ReducedMachine.NativeArithmeticPorts
import Airbender.Proofs.Trace.Retirement

namespace Airbender.ReducedMachine.NativeArithmeticExecutionProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Execute the actual native row through original nextPC preparation, the
    original operation clause and original PC retirement. RV32 wrap is retained. -/
theorem local_row_execution {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    {entry : ArithmeticProgramEntry} (fields : arithmeticDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (leftBound : (sourceWord w).Bounded)
    (rightBound : (registerOperandWord w).Bounded)
    (aligned : (w 0).val % 4 = 0) {cells : List Cell} (epoch : Nat)
    {before after : State} (history : SailHistory cells (NativeArithmeticPortProofs.nativeEvents epoch w).reverse before after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
    run (normalStep clause)
      (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  let current : Word := ⟨(w 0).val,(w 1).val⟩
  let output : Output := ⟨writtenWord w,⟨(w 13).val,(w 14).val⟩⟩
  let rebased := retiredState before current.toBitVec
  let finished := retiredState after current.toBitVec
  have rebasedHistory := Trace.Proofs.retired_state_history history current.toBitVec
  have pc : output.pc.Bounded ∧ output.pc.toBitVec = current.toBitVec + 4 :=
    NativeArithmeticPCProofs.selected_pc_successor holds fields query aligned
  have prepared := Trace.Proofs.sail_history_control rebasedHistory .nextPC (.inr rfl) output.pc.toBitVec
  have transfer : ArithmeticRegisterTransfer (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily) entry
      { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec }
      { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } :=
    ⟨NativeArithmeticPortProofs.register_reads epoch holds fields query prepared,NativeArithmeticPortProofs.register_write epoch holds fields query prepared⟩
  have pcRead : run (SailRV32.Functions.get_arch_pc ())
      { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec } =
      .ok current.toBitVec { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec } := by
    apply read_register
    simp [rebased,retiredState,Std.ExtDHashMap.get?_insert]
  obtain ⟨clause,dispatch,executed⟩ := NativeArithmeticClauseProofs.native_clause holds fields query leftBound rightBound transfer pcRead
  have projected : run (writeResult (.Regidx entry.data.rd) output.destination)
      { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec } =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } := by
    have written := transfer.2
    have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) output.destination.toBitVec)
        { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec } =
        .ok () { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } := by
      simpa [importedConstraintsMemoryPorts,MemoryPort.writeCode,WordColumns.code,
        WordColumns.evaluate,memoryWord,Nat.unpair_pair,output,writtenWord,rdWrite,rdPort,Word.toBitVec,Word.value,pairCode] using written
    simp only [writeResult]
    rw [run_bind_of_ok _ _ _ _ _ actual]
    rfl
  obtain ⟨checked,normal,projection⟩ := retire_of_destination
    (Trace.Proofs.retired_state_pc before current.toBitVec) pc.2 ⟨_,executed,projected⟩
  have written := NativeArithmeticPortProofs.register_write epoch holds fields query rebasedHistory
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) output.destination.toBitVec)
      rebased = .ok () finished := by
    simpa [importedConstraintsMemoryPorts,MemoryPort.writeCode,WordColumns.code,
      WordColumns.evaluate,memoryWord,Nat.unpair_pair,output,writtenWord,rdWrite,rdPort,Word.toBitVec,Word.value,pairCode,rebased,finished] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write entry.data.rd output actual
  have same := (EStateM.Result.ok.inj (projection.symm.trans nativeProjection)).2
  rw [same] at normal
  exact ⟨clause,dispatch,by
    simpa only [rebased,finished,current,output,Trace.Proofs.retired_state_overwrite] using normal⟩

end Airbender.ReducedMachine.NativeArithmeticExecutionProofs
