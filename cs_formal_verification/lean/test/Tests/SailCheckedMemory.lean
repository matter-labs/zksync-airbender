import Slop.Sail.VirtualMemory
import Slop.Sail.ResetState

namespace Tests.SailCheckedMemory
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

/-- The Airbender reset state with no memory. -/
private noncomputable def configured : State :=
  { resetMachine with mem := Std.ExtHashMap.emptyWithCapacity }

private theorem configuration : Configured configured := configured_reset_machine.with_mem _

private noncomputable def loaded : State := wordWriteState configured 4294967292 0xabcdef12

/-- The same configured native path admits the last RV32 byte and halfword.
    Reads come from actual initialized bytes, not a circuit-value premise. -/
theorem load_last_byte :
    Sail.run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr 0xffffffff) 1 false false false false) loaded =
        .ok (.Ok (0xab, ())) loaded := by
  apply checked_memory_read (address := 0xffffffff) (Or.inl rfl)
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · have bytes := read_subword true (offset := 3) (by decide) (by simp)
      (written_word_read configured 4294967292 0xabcdef12)
    simpa [loaded] using bytes

theorem load_last_halfword :
    Sail.run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr 0xfffffffe) 2 false false false false) loaded =
        .ok (.Ok (0xabcd, ())) loaded := by
  apply checked_memory_read (address := 0xfffffffe) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · have bytes := read_subword false (offset := 2) (by decide) (by decide)
      (written_word_read configured 4294967292 0xabcdef12)
    simpa [loaded] using bytes

private noncomputable def byteWritten : State := { loaded with mem := loaded.mem.insert 4294967295 0x80 }
private noncomputable def halfWritten : State :=
  { loaded with mem := (loaded.mem.insert 4294967294 0xff).insert 4294967295 0x80 }

theorem store_last_byte  :
    Sail.run (SailRV32.Functions.checked_mem_write (.Physaddr 0xffffffff) 1 0x80
      (.Store .Data) .PBMT_PMA .Machine () false false false) loaded =
        .ok (.Ok true) byteWritten := by
  apply checked_memory_write (address := 0xffffffff) (Or.inl rfl)
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · decide
  · rfl

theorem store_last_halfword  :
    Sail.run (SailRV32.Functions.checked_mem_write (.Physaddr 0xfffffffe) 2 0x80ff
      (.Store .Data) .PBMT_PMA .Machine () false false false) loaded =
        .ok (.Ok true) halfWritten := by
  apply checked_memory_write (address := 0xfffffffe) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · decide
  · rfl

theorem halfword_announcement :
    Sail.run (SailRV32.Functions.mem_write_ea (.Physaddr 0xfffffffe) 2 .Machine
      (.Store .Data) .PBMT_PMA false false false) loaded = .ok (.Ok ()) loaded := by
  apply checked_memory_announcement (address := 0xfffffffe) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · decide

/-- A missing second byte remains a native failure after the platform checks. -/
theorem missing_halfword_byte :
    Sail.run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr 4194304) 2 false false false false)
      { configured with mem := configured.mem.insert 4194304 0x12 } =
        .error (.OutOfMemoryRange 4194305)
          { configured with mem := configured.mem.insert 4194304 0x12 } := by
  apply checked_memory_read_error (address := 4194304) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · simp [readBytes, readByte, configured, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

theorem load_last_word :
    Sail.run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr 0xfffffffc) 4 false false false false) loaded =
        .ok (.Ok (0xabcdef12, ())) loaded := by
  apply checked_word_read (address := 0xfffffffc)
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · exact written_word_read configured 4294967292 0xabcdef12

theorem store_last_word  :
    Sail.run (SailRV32.Functions.checked_mem_write (.Physaddr 0xfffffffc) 4 0xabcdef12
      (.Store .Data) .PBMT_PMA .Machine () false false false) configured =
        .ok (.Ok true) (wordWriteState configured 4294967292 0xabcdef12) := by
  apply checked_word_write (address := 0xfffffffc) configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · decide

theorem store_announcement :
    Sail.run (SailRV32.Functions.mem_write_ea (.Physaddr 4194304) 4 .Machine
      (.Store .Data) .PBMT_PMA false false false) configured = .ok (.Ok ()) configured := by
  apply checked_word_announcement (address := 4194304) configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · decide

theorem gpr_keeps_configuration : ∃ after,
    Sail.run (SailRV32.Functions.wX_bits (.Regidx 31) 0xabcdef12) configured = .ok () after ∧
      Configured after := by
  obtain ⟨after, write, _⟩ := gpr_write_memory 31 0xabcdef12 configured
  exact ⟨after, write, configuration_gpr_write configuration 31 0xabcdef12 write⟩

theorem ram_and_pc_keep_configuration :
    Configured {
      (wordWriteState configured 4194304 0x12345678) with
      regs := configured.regs.insert .nextPC 65536 |>.insert .PC 65536 } := by
  exact configuration_pc_write (configuration_next_pc_write
    (configuration_word_write configuration 4194304 0x12345678) 65536) 65536

theorem virtual_load_last_word  :
    Sail.run (SailRV32.Functions.vmem_read (.Regidx 0) 0xfffffffc 4
      (.Load .Data) false false false) loaded = .ok (.Ok 0xabcdef12) loaded := by
  apply virtual_word_read (source := 0)
    (configuration_register_frame (before := configured) (after := loaded) rfl configuration)
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · exact written_word_read configured 4294967292 0xabcdef12

theorem virtual_store_last_word  :
    Sail.run (SailRV32.Functions.vmem_write (.Regidx 0) 0xfffffffc 4 0xabcdef12
      (.Store .Data) false false false) configured =
        .ok (.Ok true) (wordWriteState configured 4294967292 0xabcdef12) := by
  apply virtual_word_write (source := 0) configuration
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · decide

/-- Discarding LW's result still performs the original Sail memory access. -/
theorem load_discarded_result  :
    Sail.run (SailRV32.Functions.execute_LOAD 0xffc (.Regidx 0) (.Regidx 0) false 4) loaded =
      .ok SailRV32.Functions.RETIRE_SUCCESS loaded := by
  rw [load_word (show Sail.run (SailRV32.Functions.vmem_read (.Regidx 0)
    (SailRV32.Functions.sign_extend (m := 32) (0xffc : BitVec 12)) 4 (.Load .Data)
      false false false) loaded = .ok (.Ok 0xabcdef12) loaded from virtual_load_last_word)]
  rfl

theorem store_zero_register  :
    Sail.run (SailRV32.Functions.execute_STORE 0xffc (.Regidx 0) (.Regidx 0) 4) configured =
      .ok SailRV32.Functions.RETIRE_SUCCESS (wordWriteState configured 4294967292 0) := by
  apply store_word (value := 0)
  · rfl
  · apply virtual_word_write (source := 0) configuration
    · rfl
    · decide
    · unfold OrdinaryWordAddress; decide
    · decide

/-- Complete virtual accesses use original Sail address calculation, translation,
    permissions and byte memory, including the final RV32 addresses. -/
theorem virtual_load_last_byte  :
    Sail.run (SailRV32.Functions.vmem_read (.Regidx 0) 0xffffffff 1 (.Load .Data)
      false false false) loaded = .ok (.Ok 0xab) loaded := by
  apply virtual_memory_read (source := 0) (Or.inl rfl)
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · have bytes := read_subword true (offset := 3) (by decide) (by simp)
      (written_word_read configured 4294967292 0xabcdef12)
    simpa [loaded] using bytes

theorem virtual_load_last_halfword  :
    Sail.run (SailRV32.Functions.vmem_read (.Regidx 0) 0xfffffffe 2 (.Load .Data)
      false false false) loaded = .ok (.Ok 0xabcd) loaded := by
  apply virtual_memory_read (source := 0) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · have bytes := read_subword false (offset := 2) (by decide) (by decide)
      (written_word_read configured 4294967292 0xabcdef12)
    simpa [loaded] using bytes

theorem virtual_store_last_byte  :
    Sail.run (SailRV32.Functions.vmem_write (.Regidx 0) 0xffffffff 1 0x80 (.Store .Data)
      false false false) loaded = .ok (.Ok true) byteWritten := by
  apply virtual_memory_write (source := 0) (Or.inl rfl)
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · rfl

theorem virtual_store_last_halfword  :
    Sail.run (SailRV32.Functions.vmem_write (.Regidx 0) 0xfffffffe 2 0x80ff (.Store .Data)
      false false false) loaded = .ok (.Ok true) halfWritten := by
  apply virtual_memory_write (source := 0) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · rfl

theorem virtual_missing_halfword_byte  :
    Sail.run (SailRV32.Functions.vmem_read (.Regidx 0) 4194304 2 (.Load .Data)
      false false false) { configured with mem := configured.mem.insert 4194304 0x12 } =
        .error (.OutOfMemoryRange 4194305)
          { configured with mem := configured.mem.insert 4194304 0x12 } := by
  apply virtual_memory_read_error (source := 0) (Or.inr (Or.inl rfl))
  · exact configuration_register_frame (before := configured) rfl configuration
  · rfl
  · decide
  · unfold OrdinaryWordAddress; decide
  · simp [readBytes, readByte, configured, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

end Tests.SailCheckedMemory
