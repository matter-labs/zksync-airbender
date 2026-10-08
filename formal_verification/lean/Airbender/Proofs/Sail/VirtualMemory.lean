import Airbender.Proofs.Sail.CheckedMemory
import Airbender.Proofs.Sail.FlatMemory

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

private theorem configured_translation [MemoryPlatform SailRV32.exception]
    {before : State} (configuration : FlatMemoryConfiguration before)
    (address : BitVec 32) (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    run (SailRV32.Functions.translateAddr (.Virtaddr address) access .Machine) before =
      .ok (.Ok (.Physaddr (address.setWidth 34), .PBMT_PMA, ())) before := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  obtain ⟨supervisor, supervisorConfig⟩ := configuration.supervisorEnvironment
  obtain ⟨machine, machineConfig⟩ := configuration.machineEnvironment
  exact machine_translate_address initialized supervisorConfig machineConfig
    configuration.privilege address access ordinary

set_option backward.isDefEq.respectTransparency false in
theorem physical_word_read {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false false false) before =
        .ok (.Ok value) before := by
  have checked := checked_word_read configuration aligned ordinary read
  simp only [SailRV32.Functions.mem_read, SailRV32.Functions.mem_read_priv_meta, freeM_bind_assoc]
  rw [run_bind_of_ok _ _ _ _ _ checked]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem physical_word_write [MemoryPlatform SailRV32.exception]
    {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec 32) :
    run (SailRV32.Functions.mem_write_value (.Physaddr (address.setWidth 34)) 4 value
      .Machine (.Store .Data) .PBMT_PMA false false false) before =
        .ok (.Ok true) (wordWriteState before address.toNat value) := by
  have checked := checked_word_write configuration aligned ordinary value
  simp only [SailRV32.Functions.mem_write_value, SailRV32.Functions.mem_write_value_priv_meta,
    SailRV32.Functions.default_meta]
  rw [run_bind_of_ok _ _ _ _ _ checked]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem translated_word_read [MemoryPlatform SailRV32.exception]
    {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.translate_and_read_value (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .ok (.Ok (.Physaddr (address.setWidth 34), value)) before := by
  simp only [SailRV32.Functions.translate_and_read_value]
  rw [run_bind_of_ok _ _ _ _ _
    (configured_translation configuration address (.Load .Data) (by simp))]
  rw [run_bind_of_ok _ _ _ _ _ (physical_word_read configuration aligned ordinary read)]
  rfl

/-- An aligned RV32 word stays within one Sail page, including the last word. -/
theorem word_page_split (address : BitVec 32) (aligned : address.toNat % 4 = 0) :
    SailRV32.Functions.split_on_page_boundary address 4 = pure (4, 0) := by
  have shifted : (address + 3) >>> 2 = address >>> 2 := by
    apply BitVec.eq_of_toNat_eq
    have small := address.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
    change ((address.toNat + 3) % 4294967296) / 4 = address.toNat / 4
    norm_num only [Nat.reducePow] at small
    omega
  have bit_agreement (i : Nat) (large : 2 ≤ i) :
      address.getLsbD i = (address + 3).getLsbD i := by
    have bit := congrArg (fun v : BitVec 32 => v.getLsbD (i - 2)) shifted
    simpa only [BitVec.getLsbD_ushiftRight, Nat.add_sub_of_le large] using bit.symm
  have masked : address &&& 0xfffff000 = (address + 3) &&& 0xfffff000 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases bound : i < 32
    · by_cases low : i < 12
      · interval_cases i <;> simp_all
      · have bit := bit_agreement i (by omega)
        interval_cases i <;> simp_all
    · simp [BitVec.getLsbD, bound]
  have last : _root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt address 4) 1 = address + 3 := by
    change address + 4 - 1 = address + 3
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have mask : _root_.Sail.BitVec.updateSubrange (SailRV32.Functions.ones (n := 32))
      (↑SailRV32.Functions.pagesize_bits - 1 : Int).toNat 0
      (SailRV32.Functions.zeros (n := 12)) = (0xfffff000 : BitVec 32) := by decide
  simp only [SailRV32.Functions.split_on_page_boundary]
  change (if address &&& _root_.Sail.BitVec.updateSubrange
      (SailRV32.Functions.ones (n := 32)) (↑SailRV32.Functions.pagesize_bits - 1 : Int).toNat 0
      (SailRV32.Functions.zeros (n := 12)) ==
      _root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt address 4) 1 &&&
      _root_.Sail.BitVec.updateSubrange (SailRV32.Functions.ones (n := 32))
      (↑SailRV32.Functions.pagesize_bits - 1 : Int).toNat 0
      (SailRV32.Functions.zeros (n := 12)) then pure (4, 0) else _) = _
  rw [mask, last, masked]
  simp only [BEq.rfl, ite_true]

private theorem virtual_word_aligned {address : BitVec 32} (aligned : address.toNat % 4 = 0) :
    SailRV32.Functions.is_aligned_vaddr (.Virtaddr address) 4 = true := by
  change ((address.toNat : Int).tmod (4 : Nat) == 0) = true
  rw [← Int.ofNat_tmod, aligned]
  rfl

private theorem unit_bind {α : Type} (next : Unit → SailRV32.SailM α) :
    ((FreeM.pure () : SailRV32.SailM Unit) >>= next) = next () := rfl

private theorem update_word (previous value : BitVec 32) :
    _root_.Sail.BitVec.updateSubrange previous 31 0 value = value := by
  simp [_root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange']

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_address_word_read [MemoryPlatform SailRV32.exception]
    {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.vmem_read_addr (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .ok (.Ok value) before := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  have satp := machine_satp_mode initialized
  have translated := translated_word_read configuration aligned ordinary read
  simp only [SailRV32.Functions.vmem_read_addr, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [unit_bind]
    | rw [word_page_split address aligned]
    | rw [run_bind_of_ok _ _ _ _ _ satp]
    | rw [run_bind_of_ok _ _ _ _ _ translated]
    | simp [PreSail.assert, SailRV32.not,
        show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
        show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl, SailRV32.Functions.is_load_reserved,
        virtual_word_aligned aligned, SailRV32.Functions.bits_of_virtaddr,
        SailRV32.Functions.privLevel_is_virtual, SailRV32.Functions.sys_misaligned_order_decreasing,
        update_word, freeM_pure_bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_address_word_write [MemoryPlatform SailRV32.exception]
    {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec 32) :
    run (SailRV32.Functions.vmem_write_addr (.Virtaddr address) 4 value (.Store .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .ok (.Ok true) (wordWriteState before address.toNat value) := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  have satp := machine_satp_mode initialized
  have translated := configured_translation configuration address (.Store .Data) (by simp)
  have announcement := checked_word_announcement configuration aligned ordinary
  have write := physical_word_write configuration aligned ordinary value
  have extract : _root_.Sail.BitVec.extractLsb value 31 0 = value := by
    simp [_root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
  simp only [SailRV32.Functions.vmem_write_addr, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [unit_bind]
    | rw [word_page_split address aligned]
    | rw [run_bind_of_ok _ _ _ _ _ satp]
    | rw [run_bind_of_ok _ _ _ _ _ translated]
    | rw [run_bind_of_ok _ _ _ _ _ announcement]
    | rw [run_bind_of_ok _ _ _ _ _ write]
    | simp [PreSail.assert, SailRV32.not,
        show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
        show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl,
        SailRV32.Functions.is_store_conditional, virtual_word_aligned aligned,
        SailRV32.Functions.bits_of_virtaddr, SailRV32.Functions.privLevel_is_virtual,
        SailRV32.Functions.sys_misaligned_order_decreasing, extract, freeM_pure_bind]
  rfl

private theorem effective_word_address {before : State} {source : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (read : run (SailRV32.Functions.rX_bits index) before = .ok source before) :
    run (SailRV32.Functions.get_transformed_data_addr index offset access
      ⟨.Machine, 0, false⟩ 4) before = .ok (.Ext_DataAddr_OK (.Virtaddr (source + offset))) before := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  simp only [SailRV32.Functions.get_transformed_data_addr, SailRV32.Functions.ext_data_get_addr,
    freeM_bind_assoc]
  rw [run_bind_of_ok _ _ _ _ _ read]
  simp only [freeM_pure_bind, SailRV32.Functions.transform_effective_address,
    show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
    show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl,
    Bool.false_or, Bool.false_eq_true, ite_false]
  rw [freeM_bind_assoc, run_bind_of_ok _ _ _ _ _ (machine_satp_mode initialized)]
  simp [SailRV32.Functions.pm_transform_PA, SailRV32.Functions.xlen,
    SailRV32.Functions.zero_extend, _root_.Sail.BitVec.zeroExtend,
    _root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
/-- Discharge the original LW transport from a native register read and the
    history's byte read; no virtual-read success premise remains. -/
theorem virtual_word_read [MemoryPlatform SailRV32.exception]
    {before : State} {source value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % 4 = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (read : (readBytes (ue := SailRV32.exception) 4 (source + offset).toNat).run before =
      .ok value before) :
    run (SailRV32.Functions.vmem_read index offset 4 (.Load .Data) false false false) before =
      .ok (.Ok value) before := by
  have address := effective_word_address configuration index offset (.Load .Data) registerRead
  have memory := virtual_address_word_read configuration aligned ordinary read
  simp only [SailRV32.Functions.vmem_read]
  rw [run_bind_of_ok _ _ _ _ _
    (machine_access_info configuration.status configuration.privilege (.Load .Data))]
  simp only [SailRV32.Functions.vmem_read_explicit, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [run_bind_of_ok _ _ _ _ _ address]
    | rw [run_bind_of_ok _ _ _ _ _ memory]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
/-- The original SW virtual access writes exactly the native history's four
    bytes at the effective address calculated by Sail itself. -/
theorem virtual_word_write [MemoryPlatform SailRV32.exception]
    {before : State} {source : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % 4 = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (value : BitVec 32) :
    run (SailRV32.Functions.vmem_write index offset 4 value (.Store .Data) false false false) before =
      .ok (.Ok true) (wordWriteState before (source + offset).toNat value) := by
  have address := effective_word_address configuration index offset (.Store .Data) registerRead
  have memory := virtual_address_word_write configuration aligned ordinary value
  simp only [SailRV32.Functions.vmem_write]
  rw [run_bind_of_ok _ _ _ _ _
    (machine_access_info configuration.status configuration.privilege (.Store .Data))]
  simp only [SailRV32.Functions.vmem_write_explicit, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [run_bind_of_ok _ _ _ _ _ address]
    | rw [run_bind_of_ok _ _ _ _ _ memory]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem physical_word_read_error {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false false false) before =
        .error error after := by
  have checked := checked_word_read_error configuration aligned ordinary read
  simp only [SailRV32.Functions.mem_read, SailRV32.Functions.mem_read_priv_meta, freeM_bind_assoc]
  rw [run_bind_of_error _ _ _ _ _ checked]

set_option backward.isDefEq.respectTransparency false in
theorem translated_word_read_error [MemoryPlatform SailRV32.exception]
    {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.translate_and_read_value (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .error error after := by
  simp only [SailRV32.Functions.translate_and_read_value]
  rw [run_bind_of_ok _ _ _ _ _
    (configured_translation configuration address (.Load .Data) (by simp))]
  rw [run_bind_of_error _ _ _ _ _ (physical_word_read_error configuration aligned ordinary read)]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_address_word_read_error [MemoryPlatform SailRV32.exception]
    {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.vmem_read_addr (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .error error after := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  have satp := machine_satp_mode initialized
  have translated := translated_word_read_error configuration aligned ordinary read
  simp only [SailRV32.Functions.vmem_read_addr, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [unit_bind]
    | rw [word_page_split address aligned]
    | rw [run_bind_of_ok _ _ _ _ _ satp]
    | rw [run_bind_of_error _ _ _ _ _ translated]
    | simp [PreSail.assert, SailRV32.not,
        show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
        show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl, SailRV32.Functions.is_load_reserved,
        virtual_word_aligned aligned, SailRV32.Functions.bits_of_virtaddr,
        SailRV32.Functions.privLevel_is_virtual, SailRV32.Functions.sys_misaligned_order_decreasing,
        update_word, freeM_pure_bind]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
/-- Actual byte-memory failures propagate through the original LW path. -/
theorem virtual_word_read_error [MemoryPlatform SailRV32.exception]
    {before after : State} {source : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % 4 = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (read : (readBytes (ue := SailRV32.exception) 4 (source + offset).toNat).run before =
      .error error after) :
    run (SailRV32.Functions.vmem_read index offset 4 (.Load .Data) false false false) before =
      .error error after := by
  have address := effective_word_address configuration index offset (.Load .Data) registerRead
  have memory := virtual_address_word_read_error configuration aligned ordinary read
  simp only [SailRV32.Functions.vmem_read]
  rw [run_bind_of_ok _ _ _ _ _
    (machine_access_info configuration.status configuration.privilege (.Load .Data))]
  simp only [SailRV32.Functions.vmem_read_explicit, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [run_bind_of_ok _ _ _ _ _ address]
    | rw [run_bind_of_error _ _ _ _ _ memory]


end Airbender.Reference.RiscV.Sail
