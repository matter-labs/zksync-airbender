import Airbender.Proofs.Sail.CheckedMemory

namespace Tests.SailCheckedMemory
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def configured : State :=
  { (default : State) with
    mem := Std.ExtHashMap.emptyWithCapacity
    regs := (Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType).insert .mstatus 0
      |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes]
      |>.insert .mhartid 7 |>.insert .htif_tohost_base none }

set_option backward.isDefEq.respectTransparency false in
private theorem configuration : FlatMemoryConfiguration configured := by
  constructor
  · simp [configured, Std.ExtDHashMap.get?_insert]
  · simp [configured, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · simp [configured, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [configured, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [configured, Std.ExtDHashMap.get?_insert]⟩
  · simp [configured]

private def loaded : State := wordWriteState configured 4294967292 0xabcdef12

theorem load_last_word :
    Sail.run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr 0xfffffffc) 4 false false false false) loaded =
        .ok (.Ok (0xabcdef12, ())) loaded := by
  apply checked_word_read (address := 0xfffffffc)
  · exact configuration_register_frame (before := configured) (after := loaded) rfl configuration
  · decide
  · unfold OrdinaryWordAddress; decide
  · exact written_word_read configured 4294967292 0xabcdef12

theorem store_last_word [MemoryPlatform SailRV32.exception] :
    Sail.run (SailRV32.Functions.checked_mem_write (.Physaddr 0xfffffffc) 4 0xabcdef12
      (.Store .Data) .PBMT_PMA .Machine () false false false) configured =
        .ok (.Ok true) (wordWriteState configured 4294967292 0xabcdef12) := by
  apply checked_word_write (address := 0xfffffffc) configuration
  · decide
  · unfold OrdinaryWordAddress; decide

theorem store_announcement :
    Sail.run (SailRV32.Functions.mem_write_ea (.Physaddr 4194304) 4 .Machine
      (.Store .Data) .PBMT_PMA false false false) configured = .ok (.Ok ()) configured := by
  apply checked_word_announcement (address := 4194304) configuration
  · decide
  · unfold OrdinaryWordAddress; decide

theorem gpr_keeps_configuration : ∃ after,
    Sail.run (SailRV32.Functions.wX_bits (.Regidx 31) 0xabcdef12) configured = .ok () after ∧
      FlatMemoryConfiguration after := by
  obtain ⟨after, write, _⟩ := gpr_write_memory 31 0xabcdef12 configured
  exact ⟨after, write, configuration_gpr_write configuration 31 0xabcdef12 write⟩

theorem ram_and_pc_keep_configuration :
    FlatMemoryConfiguration {
      (wordWriteState configured 4194304 0x12345678) with
      regs := configured.regs.insert .nextPC 65536 |>.insert .PC 65536 } := by
  exact configuration_pc_write (configuration_next_pc_write
    (configuration_word_write configuration 4194304 0x12345678) 65536) 65536

end Tests.SailCheckedMemory
