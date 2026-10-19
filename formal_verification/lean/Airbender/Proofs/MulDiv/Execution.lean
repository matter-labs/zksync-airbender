import Airbender.Proofs.MulDiv.Clauses
import Airbender.Proofs.MulDiv.PC
import Airbender.Proofs.MulDiv.PortReads
import Airbender.Proofs.Trace.Retirement

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

/-- Execute the actual native row through original nextPC preparation, the
    original operation clause and original PC retirement. RV32 wrap is retained. -/
theorem local_row_execution {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (leftBound : (left w).Bounded)
    (aligned : (w 0).val % 4 = 0) {cells : List Cell} (epoch : Nat)
    {before after : State} (history : SailHistory cells (nativeEvents epoch w).reverse before after) :
    run (normalStep (clause entry.data.family entry.data.rs1 entry.data.rs2 entry.data.rd))
      (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  let current : Word := ⟨(w 0).val,(w 1).val⟩
  let output : Output := ⟨writtenWord w,⟨(w 13).val,(w 14).val⟩⟩
  let rebased := retiredState before current.toBitVec
  let finished := retiredState after current.toBitVec
  have rebasedHistory := Trace.Proofs.retired_state_history history current.toBitVec
  have pc := native_pc_successor (by decide) holds
    (initial := current) (final := output.pc)
    ⟨(ZMod.natCast_zmod_val _).symm,(ZMod.natCast_zmod_val _).symm,rfl,rfl⟩
    (query_inputs (by decide) fields query).1 aligned
  have prepared := Trace.Proofs.sail_history_control rebasedHistory .nextPC (.inr rfl) output.pc.toBitVec
  have transfer : RegisterTransfer (⟨.mulDiv,w⟩ : Row mersenne31Modulus MulDivFamily) entry
      { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec }
      { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } :=
    ⟨register_reads (by decide) epoch query prepared,register_write (by decide) epoch query prepared⟩
  have executed := native_clause holds fields query leftBound transfer
  have projected : run (writeResult (.Regidx entry.data.rd) output.destination)
      { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec } =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } := by
    have written := transfer.2
    have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) output.destination.toBitVec)
        { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec } =
        .ok () { finished with regs := finished.regs.insert .nextPC output.pc.toBitVec } := by
      simpa [importedConstraintsMemoryPorts,MemoryPort.writeCode,WordColumns.code,
        WordColumns.evaluate,memoryWord,Nat.unpair_pair,output,writtenWord,Word.toBitVec,Word.value,pairCode] using written
    simp only [writeResult]
    rw [run_bind_of_ok _ _ _ _ _ actual]
    rfl
  obtain ⟨checked,normal,projection⟩ := retire_of_destination
    (Trace.Proofs.retired_state_pc before current.toBitVec) pc.2 ⟨_,executed,projected⟩
  have written := register_write (by decide) epoch query rebasedHistory
  have actual : run (SailRV32.Functions.wX_bits (.Regidx entry.data.rd) output.destination.toBitVec)
      rebased = .ok () finished := by
    simpa [importedConstraintsMemoryPorts,MemoryPort.writeCode,WordColumns.code,
      WordColumns.evaluate,memoryWord,Nat.unpair_pair,output,writtenWord,Word.toBitVec,Word.value,pairCode,rebased,finished] using written
  have nativeProjection := Trace.Proofs.projected_step_of_write entry.data.rd output actual
  have same := (EStateM.Result.ok.inj (projection.symm.trans nativeProjection)).2
  rw [same] at normal
  simpa only [rebased,finished,current,output,Trace.Proofs.retired_state_overwrite] using normal

end Airbender.MulDiv.Proofs
