import Airbender.Proofs.ReducedMachine.NativeWordMemoryClauses
import Airbender.Proofs.Trace.Retirement

namespace Airbender.ReducedMachine.NativeWordMemoryRetirementProofs
open Native Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Original PC bookkeeping preserves every actual architectural cell read. -/
theorem read_control {before : State} (setter : SailRV32.Register)
    (control : setter = .PC ∨ setter = .nextPC) (pc : SailRV32.RegisterType setter)
    (cell : Cell) {value : BitVec 32} (read : cell.read before = .ok value before) :
    cell.read {before with regs := before.regs.insert setter pc} =
      .ok value {before with regs := before.regs.insert setter pc} := by
  rcases control with rfl | rfl
  · exact Trace.Proofs.cell_read_PC cell read pc
  · exact Trace.Proofs.cell_read_nextPC cell read pc

/-- Transport the PROVED actual transfer through original PC preparation.
    Keeps all OLDREADs/aliases, unmasked LW-to-x0 and actual unmasked SW RAM write. -/
theorem transfer_control {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    {before after : State} (setter : SailRV32.Register)
    (control : setter = .PC ∨ setter = .nextPC) (pc : SailRV32.RegisterType setter)
    (transfer : WordMemoryTransfer w entry before after) :
    WordMemoryTransfer w entry {before with regs := before.regs.insert setter pc}
      {after with regs := after.regs.insert setter pc} := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i kept
    exact read_control setter control pc _ (transfer.retainedReads i kept)
  · exact read_control setter control pc (.register entry.data.rs1) transfer.sourceRead
  · exact Trace.Proofs.cell_write_control setter control pc _ _ transfer.nativeWrite
  · intro load
    obtain ⟨read,write⟩ := transfer.load load
    exact ⟨read_control setter control pc _ read,
      Trace.Proofs.cell_write_control setter control pc (.register entry.data.rd) _ write⟩
  · intro store
    obtain ⟨read,write⟩ := transfer.store store
    exact ⟨read_control setter control pc (.register entry.data.rs2) read,
      Trace.Proofs.cell_write_control setter control pc (.ram (wordMemoryAddressWord w).toBitVec) _ write⟩

/-- Original normal_base_next_pc, retained LOAD/STORE and tick_pc reach the
    actual native after-state/final PC. All preparation is derived from real
    transfers/configuration and checked native PC+4/fullRV32 wrap. -/
theorem local_row_retirement [MemoryPlatform SailRV32.exception]
    {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry} {before after : State}
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (effects : WordMemoryNumericalEffects w entry) (transfer : WordMemoryTransfer w entry before after)
    (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (wordMemoryAddressWord w).toBitVec) :
    ∃ clause, wordMemoryClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord w).toBitVec) := by
  let pc := (initialPCWord w).toBitVec
  have rebased : WordMemoryTransfer w entry (retiredState before pc) (retiredState after pc) :=
    transfer_control .PC (.inl rfl) pc (transfer_control .nextPC (.inr rfl) pc transfer)
  have prepared := transfer_control .nextPC (.inr rfl) (pc+4) rebased
  have preparedConfig := configuration_next_pc_write
    (configuration_pc_write (configuration_next_pc_write configuration pc) pc) (pc+4)
  obtain ⟨clause,dispatch,executed⟩ := NativeWordMemoryClauseProofs.clause fields effects prepared preparedConfig ordinary
  have normal := normal_step_native clause (Trace.Proofs.retired_state_pc before pc) executed
  change run (normalStep clause) (retiredState before pc) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after pc) (pc+4)) at normal
  refine ⟨clause,dispatch,?_⟩
  rw [effects.pc]
  simpa only [Trace.Proofs.retired_state_overwrite] using normal

end Airbender.ReducedMachine.NativeWordMemoryRetirementProofs
