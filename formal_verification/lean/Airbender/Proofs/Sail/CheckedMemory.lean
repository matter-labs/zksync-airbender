import Airbender.Proofs.Sail.PhysicalMemory
import Airbender.Proofs.Sail.RegisterState

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

private def configurationKeys : List SailRV32.Register :=
  [.cur_privilege, .mstatus, .misa, .senvcfg, .menvcfg, .pmpcfg_n, .pmpaddr_n,
    .pma_regions, .mhartid, .htif_tohost_base]

set_option backward.isDefEq.respectTransparency false in
private theorem configuration_insert {before : State} (configuration : FlatMemoryConfiguration before)
    (key : SailRV32.Register) (value : SailRV32.RegisterType key)
    (outside : key ∉ configurationKeys) :
    FlatMemoryConfiguration { before with regs := before.regs.insert key value } := by
  have distinct (other : SailRV32.Register) (member : other ∈ configurationKeys) : key ≠ other := by
    intro same
    exact outside (same ▸ member)
  have privilege := distinct .cur_privilege (by decide)
  have status := distinct .mstatus (by decide)
  have isa := distinct .misa (by decide)
  have supervisor := distinct .senvcfg (by decide)
  have machine := distinct .menvcfg (by decide)
  have pmp := distinct .pmpcfg_n (by decide)
  have addresses := distinct .pmpaddr_n (by decide)
  have pma := distinct .pma_regions (by decide)
  have hart := distinct .mhartid (by decide)
  have htif := distinct .htif_tohost_base (by decide)
  cases configuration
  constructor <;> simp_all [Std.ExtDHashMap.get?_insert]

/-- Native RAM writes leave every configuration register unchanged. -/
theorem configuration_word_write {before : State} (configuration : FlatMemoryConfiguration before)
    (address : Nat) (value : BitVec 32) :
    FlatMemoryConfiguration (wordWriteState before address value) :=
  configuration_register_frame (before := before) (after := wordWriteState before address value)
    rfl configuration

theorem configuration_pc_write {before : State} (configuration : FlatMemoryConfiguration before)
    (value : BitVec 32) :
    FlatMemoryConfiguration { before with regs := before.regs.insert .PC value } :=
  configuration_insert configuration .PC value (by decide)

theorem configuration_next_pc_write {before : State} (configuration : FlatMemoryConfiguration before)
    (value : BitVec 32) :
    FlatMemoryConfiguration { before with regs := before.regs.insert .nextPC value } :=
  configuration_insert configuration .nextPC value (by decide)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem configuration_gpr_write {before after : State} (configuration : FlatMemoryConfiguration before)
    (index : BitVec 5) (value : BitVec 32)
    (write : run (SailRV32.Functions.wX_bits (.Regidx index) value) before = .ok () after) :
    FlatMemoryConfiguration after := by
  have primitive (key : SailRV32.Register) (data : SailRV32.RegisterType key) :
      run (do SailRV32.writeReg key data; pure ()) before =
        .ok () { before with regs := before.regs.insert key data } := rfl
  have pureRun : run (pure () : SailRV32.SailM Unit) before = .ok () before := rfl
  have bound := index.isLt
  change run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) before = _ at write
  interval_cases index.toNat
  all_goals simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, primitive, pureRun] at write
  all_goals subst after
  all_goals first
    | exact configuration
    | exact configuration_insert configuration _ _ (by decide)

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
theorem checked_word_read_error {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.checked_mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false false false false) before =
        .error error after := by
  obtain ⟨addresses, initialized⟩ := configuration.pmpAddresses
  obtain ⟨hart, hartInitialized⟩ := configuration.hart
  have permission := configured_word_permission configuration aligned (.Load .Data) (by simp)
  have pmp := machine_pmp_off configuration.pmpOff initialized
    (.Physaddr (address.setWidth 34)) 4 (.Load .Data)
  have mmio := mmio_read_excluded hartInitialized configuration.htifDisabled ordinary
  have ram := read_ram_word_error read
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
    | rw [run_bind_of_error _ _ _ _ _ ram]
    | simp [freeM_pure_bind, PreSail.assert, SailRV32.Functions.bits_of_physaddr,
        _root_.Sail.BitVec.addInt]

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
