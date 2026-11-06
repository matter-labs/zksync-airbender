import Airbender.Proofs.ReducedMachine.NativeBitwiseClause
import Airbender.Proofs.ReducedMachine.NativeBitwisePC
import Airbender.Proofs.ReducedMachine.NativeBitwisePorts
import Airbender.Proofs.Trace.Retirement

namespace Airbender.ReducedMachine.NativeBitwiseExecutionProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Execute the actual native row through original nextPC preparation, the
    original operation clause and original PC retirement. RV32 wrap is retained. -/
theorem local_row_execution {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    {entry : BitwiseProgramEntry} (fields : bitwiseDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (aligned : (w 0).val % 4 = 0) {cells : List Cell} (epoch : Nat)
    {before after : State} (history : SailHistory cells (NativeBitwisePortProofs.nativeEvents epoch w).reverse before after) :
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
    NativeBitwisePCProofs.selected_pc_successor holds fields query aligned
  have prepared := Trace.Proofs.sail_history_control rebasedHistory .nextPC (.inr rfl) output.pc.toBitVec
  have transfer : BitwiseRegisterTransfer (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily) entry
      { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec }
      { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } :=
    ⟨NativeBitwisePortProofs.register_reads epoch holds fields query prepared,NativeBitwisePortProofs.register_write epoch holds fields query prepared⟩
  obtain ⟨clause,dispatch,executed⟩ := NativeBitwiseClauseProofs.native_clause holds fields query transfer
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
  have written := NativeBitwisePortProofs.register_write epoch holds fields query rebasedHistory
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) output.destination.toBitVec)
      rebased = .ok () finished := by
    simpa [importedConstraintsMemoryPorts,MemoryPort.writeCode,WordColumns.code,
      WordColumns.evaluate,memoryWord,Nat.unpair_pair,output,writtenWord,rdWrite,rdPort,Word.toBitVec,Word.value,pairCode,rebased,finished] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write entry.data.rd output actual
  have same := (EStateM.Result.ok.inj (projection.symm.trans nativeProjection)).2
  rw [same] at normal
  exact ⟨clause,dispatch,by
    simpa only [rebased,finished,current,output,Trace.Proofs.retired_state_overwrite] using normal⟩

end Airbender.ReducedMachine.NativeBitwiseExecutionProofs
