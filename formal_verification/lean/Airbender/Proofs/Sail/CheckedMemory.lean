import Airbender.Proofs.Sail.PhysicalMemory

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

private theorem native_unit_bind {α : Type} (next : Unit → SailRV32.SailM α) :
    ((FreeM.pure () : SailRV32.SailM Unit) >>= next) = next () := rfl

theorem configuration_register_frame {before after : State}
    (registers : after.regs = before.regs) (configuration : FlatMemoryConfiguration before) :
    FlatMemoryConfiguration after := by
  cases configuration
  constructor <;> simp_all only

theorem configured_word_permission {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    run (SailRV32.Functions.check_pma_with_pmp_priority access .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false) before =
        .ok (.Ok ⟨.CannotSplit, 0⟩) before := by
  obtain ⟨attributes, regions, readable, writable, executable⟩ := configuration.pma
  simp only [SailRV32.Functions.check_pma_with_pmp_priority]
  rw [run_bind_of_ok _ _ _ _ _
    (pma_word_access regions readable writable executable aligned access ordinary)]
  rfl

private theorem no_split_word (address : SailRV32.physaddr) :
    SailRV32.Functions.split_misaligned address 4 0 .CannotSplit = pure (1, 4) := by
  cases address
  rfl

private theorem whole_word_update (previous value : BitVec 32) :
    _root_.Sail.BitVec.updateSubrange previous 31 0 value = value := by
  simp [_root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange']

theorem word_address_announcement (before : State) (address : BitVec 32) :
    run (SailRV32.Functions.write_ram_ea .Write_plain (.Store .Data)
      (.Physaddr (address.setWidth 34)) 4) before = .ok () before := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem checked_word_read {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false false false false) before =
        .ok (.Ok (value, ())) before := by
  obtain ⟨addresses, initialized⟩ := configuration.pmpAddresses
  obtain ⟨hart, hartInitialized⟩ := configuration.hart
  have permission := configured_word_permission configuration aligned (.Load .Data) (by simp)
  have pmp := machine_pmp_off configuration.pmpOff initialized
    (.Physaddr (address.setWidth 34)) 4 (.Load .Data)
  have mmio := mmio_read_excluded hartInitialized configuration.htifDisabled ordinary
  have ram := read_ram_word read
  simp only [SailRV32.Functions.checked_mem_read, SailRV32.SailME.run]
  repeat rw [freeM_bind_assoc]
  rw [early_return_lift_bind, run_bind_of_ok _ _ _ _ _ permission]
  simp only [freeM_pure_bind]
  rw [early_return_lift_bind, no_split_word, freeM_pure_bind]
  simp [SailRV32.Functions.misaligned_order, SailRV32.Functions.sys_misaligned_order_decreasing,
    SailRV32.Functions.read_kind_of_flags, untilFuelM, untilFuelM.go, freeM_pure_bind]
  repeat first
    | rw [native_unit_bind]
    | rw [freeM_pure_bind]
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [run_bind_of_ok _ _ _ _ _ pmp]
    | rw [run_bind_of_ok _ _ _ _ _ mmio]
    | rw [run_bind_of_ok _ _ _ _ _ ram]
    | simp [freeM_pure_bind, PreSail.assert, SailRV32.Functions.bits_of_physaddr,
        _root_.Sail.BitVec.addInt]
  rw [whole_word_update]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem checked_word_write [MemoryPlatform SailRV32.exception] {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec 32) :
    run (SailRV32.Functions.checked_mem_write (.Physaddr (address.setWidth 34)) 4 value
      (.Store .Data) .PBMT_PMA .Machine () false false false) before =
        .ok (.Ok true) (wordWriteState before address.toNat value) := by
  obtain ⟨addresses, initialized⟩ := configuration.pmpAddresses
  obtain ⟨hart, hartInitialized⟩ := configuration.hart
  have permission := configured_word_permission configuration aligned (.Store .Data) (by simp)
  have pmp := machine_pmp_off configuration.pmpOff initialized
    (.Physaddr (address.setWidth 34)) 4 (.Store .Data)
  have mmio := mmio_write_excluded hartInitialized configuration.htifDisabled ordinary
  have ram := write_ram_word before address value
  simp only [SailRV32.Functions.checked_mem_write, SailRV32.SailME.run]
  repeat rw [freeM_bind_assoc]
  rw [early_return_lift_bind, run_bind_of_ok _ _ _ _ _ permission]
  simp only [freeM_pure_bind]
  rw [early_return_lift_bind, no_split_word, freeM_pure_bind]
  simp [SailRV32.Functions.misaligned_order, SailRV32.Functions.sys_misaligned_order_decreasing,
    SailRV32.Functions.write_kind_of_flags, untilFuelM, untilFuelM.go, freeM_pure_bind]
  repeat first
    | rw [native_unit_bind]
    | rw [freeM_pure_bind]
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [run_bind_of_ok _ _ _ _ _ pmp]
    | rw [run_bind_of_ok _ _ _ _ _ mmio]
    | rw [run_bind_of_ok _ _ _ _ _ ram]
    | simp [freeM_pure_bind, PreSail.assert, SailRV32.Functions.bits_of_physaddr,
        _root_.Sail.BitVec.addInt, _root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem checked_word_announcement {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address) :
    run (SailRV32.Functions.mem_write_ea (.Physaddr (address.setWidth 34)) 4 .Machine
      (.Store .Data) .PBMT_PMA false false false) before = .ok (.Ok ()) before := by
  obtain ⟨addresses, initialized⟩ := configuration.pmpAddresses
  obtain ⟨hart, hartInitialized⟩ := configuration.hart
  have permission := configured_word_permission configuration aligned (.Store .Data) (by simp)
  have pmp := machine_pmp_off configuration.pmpOff initialized
    (.Physaddr (address.setWidth 34)) 4 (.Store .Data)
  have mmio := mmio_write_excluded hartInitialized configuration.htifDisabled ordinary
  have announce := word_address_announcement before address
  simp only [SailRV32.Functions.mem_write_ea, SailRV32.SailME.run]
  repeat rw [freeM_bind_assoc]
  rw [early_return_lift_bind, run_bind_of_ok _ _ _ _ _ permission]
  simp only [freeM_pure_bind]
  rw [early_return_lift_bind, no_split_word, freeM_pure_bind]
  simp [SailRV32.Functions.misaligned_order, SailRV32.Functions.sys_misaligned_order_decreasing,
    SailRV32.Functions.write_kind_of_flags, untilFuelM, untilFuelM.go, freeM_pure_bind]
  repeat first
    | rw [native_unit_bind]
    | rw [freeM_pure_bind]
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [run_bind_of_ok _ _ _ _ _ pmp]
    | rw [run_bind_of_ok _ _ _ _ _ mmio]
    | rw [run_bind_of_ok _ _ _ _ _ announce]
    | simp [freeM_pure_bind, PreSail.assert, SailRV32.Functions.bits_of_physaddr,
        _root_.Sail.BitVec.addInt, SailRV32.not]
  rfl

end Airbender.Reference.RiscV.Sail
