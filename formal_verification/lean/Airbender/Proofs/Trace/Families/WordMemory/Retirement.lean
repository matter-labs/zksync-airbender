import Airbender.Proofs.Trace.Families.WordMemory.RAMExecution
import Airbender.Proofs.Trace.Families.WordMemory.ROMExecution
import Airbender.Proofs.Trace.Retirement

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- Original Sail nextPC preparation, native-derived memory execution and PC
    retirement reach the same actual cell state at the modular successor PC.
    Control reads and prepared memory effects are derived, not supplied. -/
theorem projected_ram_load_retirement {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (ram : 64 ≤ (w 20).val) (ordinary : OrdinaryWordAddress (addressWord w).toBitVec)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) (pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4)) (retiredState before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (pc + 4)) := by
  have preparedConfig := configuration_next_pc_write
    (configuration_pc_write (configuration_next_pc_write configuration pc) pc) (pc + 4)
  have preparedHistory := Trace.Proofs.sail_history_control
    (Trace.Proofs.retired_state_history history pc) .nextPC (.inr rfl) (pc + 4)
  have executed := projected_ram_load_execution hp epoch native address fields query instruction
    preparedConfig ram ordinary preparedHistory
  have checked := normal_step_native (before := retiredState before pc)
    (after := retiredState after pc) _ (Trace.Proofs.retired_state_pc before pc) executed
  change run (normalStep _) (retiredState before pc) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after pc) (pc + 4)) at checked
  simpa only [Trace.Proofs.retired_state_overwrite] using checked

set_option backward.isDefEq.respectTransparency false in
/-- Original Sail nextPC preparation, native-derived memory execution and PC
    retirement reach the same actual cell state at the modular successor PC.
    Control reads and prepared memory effects are derived, not supplied. -/
theorem projected_ram_store_retirement {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rs2 : BitVec 5}
    (instruction : entry.instruction = .STORE (imm, .Regidx rs2, .Regidx rs1, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    (ordinary : OrdinaryWordAddress (addressWord w).toBitVec)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) (pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4)) (retiredState before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (pc + 4)) := by
  have preparedConfig := configuration_next_pc_write
    (configuration_pc_write (configuration_next_pc_write configuration pc) pc) (pc + 4)
  have preparedHistory := Trace.Proofs.sail_history_control
    (Trace.Proofs.retired_state_history history pc) .nextPC (.inr rfl) (pc + 4)
  have executed := projected_ram_store_execution hp epoch native address fields query instruction
    preparedConfig ordinary preparedHistory
  have checked := normal_step_native (before := retiredState before pc)
    (after := retiredState after pc) _ (Trace.Proofs.retired_state_pc before pc) executed
  change run (normalStep _) (retiredState before pc) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after pc) (pc + 4)) at checked
  simpa only [Trace.Proofs.retired_state_overwrite] using checked

set_option backward.isDefEq.respectTransparency false in
/-- Original Sail nextPC preparation, native-derived memory execution and PC
    retirement reach the same actual cell state at the modular successor PC.
    Control reads and prepared memory effects are derived, not supplied. -/
theorem projected_rom_load_retirement {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 4194304 < p) {rom : WordROM} {cells : List Cell} {w : Nat → ZMod p} (epoch : Nat)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (address : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec)
    {entry : ProgramEntry WordMemoryFamily}
    (fields : decoderFields entry.instruction = some entry.data)
    (query : (⟨.wordMemory, w⟩ : Row p WordMemoryFamily).decoderQuery = entry.query)
    {imm : BitVec 12} {rs1 rd : BitVec 5}
    (instruction : entry.instruction = .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
    {before after : State} (configuration : FlatMemoryConfiguration before)
    {count : Nat} (image : wordROMImage before count = some rom)
    (region : (addressWord w).hi < 64) (within : (addressWord w).value < 4 * count)
    (history : SailHistory cells
      ((rowEvents epoch (⟨.wordMemory, w⟩ : Row p WordMemoryFamily)).reverse.filter
        fun event => architecturalAddress event.2.1) before after) (pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4)) (retiredState before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (pc + 4)) := by
  have preparedConfig := configuration_next_pc_write
    (configuration_pc_write (configuration_next_pc_write configuration pc) pc) (pc + 4)
  have preparedHistory := Trace.Proofs.sail_history_control
    (Trace.Proofs.retired_state_history history pc) .nextPC (.inr rfl) (pc + 4)
  have preparedImage : wordROMImage
      { (retiredState before pc) with regs := (retiredState before pc).regs.insert .nextPC (pc + 4) }
      count = some rom := rom_image_after_frame (by intro key bound; rfl) image
  have executed := projected_rom_load_execution hp epoch native address fields query instruction
    preparedConfig preparedImage region within preparedHistory
  have checked := normal_step_native (before := retiredState before pc)
    (after := retiredState after pc) _ (Trace.Proofs.retired_state_pc before pc) executed
  change run (normalStep _) (retiredState before pc) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after pc) (pc + 4)) at checked
  simpa only [Trace.Proofs.retired_state_overwrite] using checked

end Airbender.WordMemory.Proofs
