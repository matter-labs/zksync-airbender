import Airbender.Proofs.ReducedMachine.NativeWordMemoryTransfers
import Airbender.Proofs.ReducedMachine.NativeWordMemoryRetirement
import Airbender.Proofs.ReducedMachine.NativeROMImage

namespace Tests.NativeReducedWordMemoryRetirement
open Airbender ReducedMachine Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }
private def configured (isa address : BitVec 32) : State :=
  { (default : State) with
    regs := ((Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 address |>.insert .x2 (123 : BitVec 32)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa isa
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0) |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes] |>.insert .mhartid 7 |>.insert .htif_tohost_base none)
    mem := Std.ExtHashMap.emptyWithCapacity }
private theorem configured_privilege (isa address : BitVec 32) :
    (configured isa address).regs.get? .cur_privilege = some .Machine := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_status (isa address : BitVec 32) :
    (configured isa address).regs.get? .mstatus = some 0 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_isa (isa address : BitVec 32) :
    (configured isa address).regs.get? .misa = some isa := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_supervisor (isa address : BitVec 32) :
    (configured isa address).regs.get? .senvcfg = some 0 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_machine (isa address : BitVec 32) :
    (configured isa address).regs.get? .menvcfg = some 0x10 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_pmp (isa address : BitVec 32) :
    (configured isa address).regs.get? .pmpcfg_n = some (Vector.replicate 64 0) := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_pmpAddresses (isa address : BitVec 32) :
    (configured isa address).regs.get? .pmpaddr_n = some (Vector.replicate 64 0) := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_pma (isa address : BitVec 32) :
    (configured isa address).regs.get? .pma_regions = some [rv32Region attributes] := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_hart (isa address : BitVec 32) :
    (configured isa address).regs.get? .mhartid = some 7 := by
  simp [configured,Std.ExtDHashMap.get?_insert]

private theorem configured_htif (isa address : BitVec 32) :
    (configured isa address).regs.get? .htif_tohost_base = some none := by
  simp [configured]
  rfl

private theorem configuration (isa address : BitVec 32) : FlatMemoryConfiguration (configured isa address) :=
  ⟨configured_privilege isa address,configured_status isa address,⟨isa,configured_isa isa address⟩,
    ⟨0,configured_supervisor isa address⟩,⟨0x10,configured_machine isa address⟩,
    configured_pmp isa address,⟨Vector.replicate 64 0,configured_pmpAddresses isa address⟩,
    ⟨attributes,configured_pma isa address,rfl,rfl,rfl⟩,⟨7,configured_hart isa address⟩,configured_htif isa address⟩


private def prepared (before : State) (pc : BitVec 32) : State :=
  {retiredState before pc with regs := (retiredState before pc).regs.insert .nextPC (pc+4)}
private theorem prepared_read {before : State} (pc : BitVec 32) (cell : Cell) {value : BitVec 32}
    (read : cell.read before = .ok value before) : cell.read (prepared before pc) = .ok value (prepared before pc) :=
  NativeWordMemoryRetirementProofs.read_control .nextPC (.inr rfl) (pc+4) cell
    (Trace.Proofs.cell_read_PC cell (Trace.Proofs.cell_read_nextPC cell read pc) pc)
private theorem prepared_write {before after : State} (pc : BitVec 32) (cell : Cell) (value : BitVec 32)
    (write : run (cell.write value) before = .ok () after) :
    run (cell.write value) (prepared before pc) = .ok () (prepared after pc) :=
  Trace.Proofs.cell_write_control .nextPC (.inr rfl) (pc+4) cell value
    (Trace.Proofs.cell_write_control .PC (.inl rfl) pc cell value
      (Trace.Proofs.cell_write_control .nextPC (.inr rfl) pc cell value write))
private theorem prepared_config {before : State} (config : FlatMemoryConfiguration before) (pc : BitVec 32) :
    FlatMemoryConfiguration (prepared before pc) :=
  configuration_next_pc_write (configuration_pc_write (configuration_next_pc_write config pc) pc) (pc+4)

private theorem load_normal [MemoryPlatform SailRV32.exception] {before : State}
    (config : FlatMemoryConfiguration before)
    (source : (Cell.register 1).read before = .ok (16 : BitVec 32) before)
    (memory : (Cell.ram 16).read before = .ok (21015 : BitVec 32) before) (pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4))
      (retiredState before pc) = .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState before (pc+4)) := by
  have read := virtual_word_read (prepared_config config pc) (.Regidx 1) (0 : BitVec 32)
    (prepared_read pc _ source) (by decide) (by unfold OrdinaryWordAddress; decide) (prepared_read pc _ memory)
  have offset : SailRV32.Functions.sign_extend (m := 32) (0 : BitVec 12) = (0 : BitVec 32) := by decide
  rw [← offset] at read
  have executed : run (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4) (prepared before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (prepared before pc) := by
    rw [load_word read,run_bind_of_ok _ _ _ _ _ (NativeWordMemoryTransferProofs.zero_register_write (prepared before pc) 21015)]
    rfl
  have normal := normal_step_native _ (Trace.Proofs.retired_state_pc before pc) executed
  change run (normalStep _) (retiredState before pc) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState before pc) (pc+4)) at normal
  simpa only [Trace.Proofs.retired_state_overwrite] using normal

private theorem rom_configuration (isa : BitVec 32) : FlatMemoryConfiguration (NativeROM.state (configured isa 16)) :=
  configuration_register_frame (NativeROMProofs.registers _) (configuration isa 16)
private theorem rom_source (isa : BitVec 32) :
    (Cell.register 1).read (NativeROM.state (configured isa 16)) =
      .ok (16 : BitVec 32) (NativeROM.state (configured isa 16)) := by
  apply read_register
  change (NativeROM.state (configured isa 16)).regs.get? .x1 = some (16 : BitVec 32)
  rw [NativeROMProofs.registers]
  simp [configured,Std.ExtDHashMap.get?_insert]
private theorem rom_read (isa : BitVec 32) :
    (Cell.ram 16).read (NativeROM.state (configured isa 16)) =
      .ok (21015 : BitVec 32) (NativeROM.state (configured isa 16)) := by
  have actual := NativeROMProofs.numerical_read (configured isa 16) ⟨4,by decide⟩
  simpa [wordMemoryROMWord,NativeFixed.wordROMValue,Word.toBitVec,Word.value,limbBase] using actual

/-- Positive ORIGINAL normal LW-to-x0 at EVERY RV32 PC, including rollover.
    Concrete original ROM21015 is read before the unmasked x0 write is discarded.
    This is reference execution, not a full117-equation accepted native witness. -/
theorem original_load_x0_normal [MemoryPlatform SailRV32.exception] (isa pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_LOAD 0 (.Regidx 1) (.Regidx 0) false 4))
      (retiredState (NativeROM.state (configured isa 16)) pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (NativeROM.state (configured isa 16)) (pc+4)) :=
  load_normal (rom_configuration isa) (rom_source isa) (rom_read isa) pc

set_option backward.isDefEq.respectTransparency false in
private theorem store_normal [MemoryPlatform SailRV32.exception] {before : State}
    (config : FlatMemoryConfiguration before)
    (first : (Cell.register 1).read before = .ok (4194304 : BitVec 32) before)
    (second : (Cell.register 2).read before = .ok (123 : BitVec 32) before) (pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_STORE 0 (.Regidx 2) (.Regidx 1) 4))
      (retiredState before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (wordWriteState before 4194304 123) (pc+4)) := by
  let after := wordWriteState before 4194304 123
  have written : run (writeMemory (size := 4) (4194304 : BitVec 32) (123 : BitVec 32))
      (prepared before pc) = .ok () (prepared after pc) :=
    prepared_write pc (.ram 4194304) 123 (write_word_state before 4194304 123)
  have write := virtual_memory_write (Or.inr (Or.inr rfl)) (prepared_config config pc)
    (.Regidx 1) (0 : BitVec 32) (prepared_read pc _ first) (by decide)
    (by unfold OrdinaryWordAddress; decide) (123 : BitVec 32) written
  have offset : SailRV32.Functions.sign_extend (m := 32) (0 : BitVec 12) = (0 : BitVec 32) := by decide
  rw [← offset] at write
  have executed := store_word (prepared_read pc _ second) write
  have normal := normal_step_native _ (Trace.Proofs.retired_state_pc before pc) executed
  change run (normalStep _) (retiredState before pc) =
    .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after pc) (pc+4)) at normal
  simpa only [after,Trace.Proofs.retired_state_overwrite] using normal

private theorem ram_source (isa : BitVec 32) : (Cell.register 1).read (configured isa 4194304) =
    .ok (4194304 : BitVec 32) (configured isa 4194304) := by
  apply read_register; simp [configured,Std.ExtDHashMap.get?_insert]
private theorem ram_value (isa : BitVec 32) : (Cell.register 2).read (configured isa 4194304) =
    .ok (123 : BitVec 32) (configured isa 4194304) := by
  apply read_register; simp [configured,Std.ExtDHashMap.get?_insert]

/-- Positive ORIGINAL normal SW retains its actual RAM write at EVERY RV32
    successor. No dummy rd masking or supplied memory result is used. -/
theorem original_store_normal [MemoryPlatform SailRV32.exception] (isa pc : BitVec 32) :
    run (normalStep (SailRV32.Functions.execute_STORE 0 (.Regidx 2) (.Regidx 1) 4))
      (retiredState (configured isa 4194304) pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (wordWriteState (configured isa 4194304) 4194304 123) (pc+4)) :=
  store_normal (configuration isa 4194304) (ram_source isa) (ram_value isa) pc

/-- Independent numerical endpoints for the actual normal retirement theorem. -/
theorem retirement_wrap_endpoints :
    (0xfffffffc : BitVec 32)+4 = 0 ∧ (0xffffffff : BitVec 32)+4 = 3 ∧ (0 : BitVec 32)+4 = 4 := by decide

end Tests.NativeReducedWordMemoryRetirement
