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
theorem physical_memory_read {size : Nat} {before : State} {address : BitVec 32} {value : BitVec (8 * size)}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) size false false false) before = .ok (.Ok value) before := by
  have checked := checked_memory_read width configuration aligned ordinary read
  simp only [SailRV32.Functions.mem_read, SailRV32.Functions.mem_read_priv_meta, freeM_bind_assoc]
  rw [run_bind_of_ok _ _ _ _ _ checked]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem physical_memory_write [MemoryPlatform SailRV32.exception]
    {size : Nat} {before after : State} {address : BitVec 32}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec (8 * size))
    (write : run (writeMemory (size := size) address value) before = .ok () after) :
    run (SailRV32.Functions.mem_write_value (.Physaddr (address.setWidth 34)) size value
      .Machine (.Store .Data) .PBMT_PMA false false false) before = .ok (.Ok true) after := by
  have checked := checked_memory_write width configuration aligned ordinary value write
  simp only [SailRV32.Functions.mem_write_value, SailRV32.Functions.mem_write_value_priv_meta,
    SailRV32.Functions.default_meta]
  rw [run_bind_of_ok _ _ _ _ _ checked]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem translated_memory_read [MemoryPlatform SailRV32.exception]
    {size : Nat} {before : State} {address : BitVec 32} {value : BitVec (8 * size)}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.translate_and_read_value (.Virtaddr address) size (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .ok (.Ok (.Physaddr (address.setWidth 34), value)) before := by
  simp only [SailRV32.Functions.translate_and_read_value]
  rw [run_bind_of_ok _ _ _ _ _
    (configured_translation configuration address (.Load .Data) (by simp))]
  rw [run_bind_of_ok _ _ _ _ _ (physical_memory_read width configuration aligned ordinary read)]
  rfl

/-- Aligned byte/halfword/word accesses stay within one Sail page, including
    the end of the RV32 address space. -/
theorem memory_page_split (address : BitVec 32) {size : Nat}
    (width : size = 1 ∨ size = 2 ∨ size = 4) (aligned : address.toNat % size = 0) :
    SailRV32.Functions.split_on_page_boundary address size = pure ((size : Int), 0) := by
  have shifted : (address + BitVec.ofNat 32 (size - 1)) >>> 2 = address >>> 2 := by
    apply BitVec.eq_of_toNat_eq
    have small := address.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num only [Nat.reducePow] at small ⊢
    rcases width with rfl | rfl | rfl <;> omega
  have bit_agreement (i : Nat) (large : 2 ≤ i) :
      address.getLsbD i = (address + BitVec.ofNat 32 (size - 1)).getLsbD i := by
    have bit := congrArg (fun v : BitVec 32 => v.getLsbD (i - 2)) shifted
    simpa only [BitVec.getLsbD_ushiftRight, Nat.add_sub_of_le large] using bit.symm
  have masked : address &&& 0xfffff000 = (address + BitVec.ofNat 32 (size - 1)) &&& 0xfffff000 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases bound : i < 32
    · by_cases low : i < 12
      · interval_cases i <;> simp_all
      · have bit := bit_agreement i (by omega)
        interval_cases i <;> simp_all
    · simp [BitVec.getLsbD, bound]
  have last : _root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt address size) 1 =
      address + BitVec.ofNat 32 (size - 1) := by
    rcases width with rfl | rfl | rfl
    all_goals change address + _ - 1 = address + _
    all_goals rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    all_goals rfl
  have mask : _root_.Sail.BitVec.updateSubrange (SailRV32.Functions.ones (n := 32))
      (↑SailRV32.Functions.pagesize_bits - 1 : Int).toNat 0
      (SailRV32.Functions.zeros (n := 12)) = (0xfffff000 : BitVec 32) := by decide
  simp only [SailRV32.Functions.split_on_page_boundary]
  change (if address &&& _root_.Sail.BitVec.updateSubrange
      (SailRV32.Functions.ones (n := 32)) (↑SailRV32.Functions.pagesize_bits - 1 : Int).toNat 0
      (SailRV32.Functions.zeros (n := 12)) ==
      _root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt address size) 1 &&&
      _root_.Sail.BitVec.updateSubrange (SailRV32.Functions.ones (n := 32))
      (↑SailRV32.Functions.pagesize_bits - 1 : Int).toNat 0
      (SailRV32.Functions.zeros (n := 12)) then (pure ((size : Int), 0) : SailRV32.SailM (Int × Int)) else _) = _
  rw [mask, last, masked]
  simp only [BEq.rfl, ite_true]

private theorem virtual_memory_aligned {size : Nat} {address : BitVec 32}
    (aligned : address.toNat % size = 0) :
    SailRV32.Functions.is_aligned_vaddr (.Virtaddr address) size = true := by
  change ((address.toNat : Int).tmod size == 0) = true
  rw [← Int.ofNat_tmod, aligned]
  rfl

private theorem unit_bind {α : Type} (next : Unit → SailRV32.SailM α) :
    ((FreeM.pure () : SailRV32.SailM Unit) >>= next) = next () := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_address_memory_read [MemoryPlatform SailRV32.exception]
    {size : Nat} {before : State} {address : BitVec 32} {value : BitVec (8 * size)}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.vmem_read_addr (.Virtaddr address) size (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .ok (.Ok value) before := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  have satp := machine_satp_mode initialized
  have translated := translated_memory_read width configuration aligned ordinary read
  simp only [SailRV32.Functions.vmem_read_addr, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [unit_bind]
    | rw [memory_page_split address width aligned]
    | rw [run_bind_of_ok _ _ _ _ _ satp]
    | rw [run_bind_of_ok _ _ _ _ _ translated]
    | simp [PreSail.assert, SailRV32.not,
        show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
        show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl, SailRV32.Functions.is_load_reserved,
        virtual_memory_aligned aligned, SailRV32.Functions.bits_of_virtaddr,
        SailRV32.Functions.privLevel_is_virtual, SailRV32.Functions.sys_misaligned_order_decreasing,
        freeM_pure_bind]
  rcases width with rfl | rfl | rfl
  all_goals simp [_root_.Sail.BitVec.updateSubrange, _root_.Sail.BitVec.updateSubrange']
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_address_memory_write [MemoryPlatform SailRV32.exception]
    {size : Nat} {before after : State} {address : BitVec 32}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec (8 * size))
    (write : run (writeMemory (size := size) address value) before = .ok () after) :
    run (SailRV32.Functions.vmem_write_addr (.Virtaddr address) size value (.Store .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .ok (.Ok true) after := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  have satp := machine_satp_mode initialized
  have translated := configured_translation configuration address (.Store .Data) (by simp)
  have announcement := checked_memory_announcement width configuration aligned ordinary
  have write := physical_memory_write width configuration aligned ordinary value write
  simp only [SailRV32.Functions.vmem_write_addr, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [unit_bind]
    | rw [memory_page_split address width aligned]
    | rw [run_bind_of_ok _ _ _ _ _ satp]
    | rw [run_bind_of_ok _ _ _ _ _ translated]
    | rw [run_bind_of_ok _ _ _ _ _ announcement]
    | rw [run_bind_of_ok _ _ _ _ _ write]
    | simp [PreSail.assert, SailRV32.not,
        show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
        show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl,
        SailRV32.Functions.is_store_conditional, virtual_memory_aligned aligned,
        SailRV32.Functions.bits_of_virtaddr, SailRV32.Functions.privLevel_is_virtual,
        SailRV32.Functions.sys_misaligned_order_decreasing, freeM_pure_bind]
  rcases width with rfl | rfl | rfl
  all_goals
    simp [_root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
    rw [run_bind_of_ok _ _ _ _ _ write]
    rfl

private theorem effective_memory_address {before : State} {source : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32) (size : Nat)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (read : run (SailRV32.Functions.rX_bits index) before = .ok source before) :
    run (SailRV32.Functions.get_transformed_data_addr index offset access
      ⟨.Machine, 0, false⟩ size) before = .ok (.Ext_DataAddr_OK (.Virtaddr (source + offset))) before := by
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
theorem virtual_memory_read [MemoryPlatform SailRV32.exception]
    {size : Nat} {before : State} {source : BitVec 32} {value : BitVec (8 * size)}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % size = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (read : (readBytes (ue := SailRV32.exception) size (source + offset).toNat).run before = .ok value before) :
    run (SailRV32.Functions.vmem_read index offset size (.Load .Data) false false false) before =
      .ok (.Ok value) before := by
  have address := effective_memory_address configuration index offset size (.Load .Data) registerRead
  have memory := virtual_address_memory_read width configuration aligned ordinary read
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
theorem virtual_memory_write [MemoryPlatform SailRV32.exception]
    {size : Nat} {before after : State} {source : BitVec 32}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % size = 0) (ordinary : OrdinaryWordAddress (source + offset)) (value : BitVec (8 * size))
    (write : run (writeMemory (size := size) (source + offset) value) before = .ok () after) :
    run (SailRV32.Functions.vmem_write index offset size value (.Store .Data) false false false) before =
      .ok (.Ok true) after := by
  have address := effective_memory_address configuration index offset size (.Store .Data) registerRead
  have memory := virtual_address_memory_write width configuration aligned ordinary value write
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
theorem physical_memory_read_error {size : Nat} {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before = .error error after) :
    run (SailRV32.Functions.mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) size false false false) before = .error error after := by
  have checked := checked_memory_read_error width configuration aligned ordinary read
  simp only [SailRV32.Functions.mem_read, SailRV32.Functions.mem_read_priv_meta, freeM_bind_assoc]
  rw [run_bind_of_error _ _ _ _ _ checked]

set_option backward.isDefEq.respectTransparency false in
theorem translated_memory_read_error [MemoryPlatform SailRV32.exception]
    {size : Nat} {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before = .error error after) :
    run (SailRV32.Functions.translate_and_read_value (.Virtaddr address) size (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .error error after := by
  simp only [SailRV32.Functions.translate_and_read_value]
  rw [run_bind_of_ok _ _ _ _ _
    (configured_translation configuration address (.Load .Data) (by simp))]
  rw [run_bind_of_error _ _ _ _ _ (physical_memory_read_error width configuration aligned ordinary read)]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_address_memory_read_error [MemoryPlatform SailRV32.exception]
    {size : Nat} {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % size = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) size address.toNat).run before = .error error after) :
    run (SailRV32.Functions.vmem_read_addr (.Virtaddr address) size (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .error error after := by
  obtain ⟨isa, initialized⟩ := configuration.isa
  have satp := machine_satp_mode initialized
  have translated := translated_memory_read_error width configuration aligned ordinary read
  simp only [SailRV32.Functions.vmem_read_addr, SailRV32.SailME.run]
  repeat first
    | rw [freeM_bind_assoc]
    | rw [early_return_lift_bind]
    | rw [freeM_pure_bind]
    | rw [unit_bind]
    | rw [memory_page_split address width aligned]
    | rw [run_bind_of_ok _ _ _ _ _ satp]
    | rw [run_bind_of_error _ _ _ _ _ translated]
    | simp [PreSail.assert, SailRV32.not,
        show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
        show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl, SailRV32.Functions.is_load_reserved,
        virtual_memory_aligned aligned, SailRV32.Functions.bits_of_virtaddr,
        SailRV32.Functions.privLevel_is_virtual, SailRV32.Functions.sys_misaligned_order_decreasing,
        freeM_pure_bind]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem virtual_memory_read_error [MemoryPlatform SailRV32.exception]
    {size : Nat} {before after : State}
    {error : _root_.Sail.Error SailRV32.exception} {source : BitVec 32}
    (width : size = 1 ∨ size = 2 ∨ size = 4)
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % size = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (read : (readBytes (ue := SailRV32.exception) size (source + offset).toNat).run before = .error error after) :
    run (SailRV32.Functions.vmem_read index offset size (.Load .Data) false false false) before =
      .error error after := by
  have address := effective_memory_address configuration index offset size (.Load .Data) registerRead
  have memory := virtual_address_memory_read_error width configuration aligned ordinary read
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

theorem physical_word_read {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false false false) before =
        .ok (.Ok value) before :=
  physical_memory_read (Or.inr (Or.inr rfl)) configuration aligned ordinary read

theorem physical_word_write [MemoryPlatform SailRV32.exception]
    {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec 32) :
    run (SailRV32.Functions.mem_write_value (.Physaddr (address.setWidth 34)) 4 value
      .Machine (.Store .Data) .PBMT_PMA false false false) before =
        .ok (.Ok true) (wordWriteState before address.toNat value) :=
  physical_memory_write (Or.inr (Or.inr rfl)) configuration aligned ordinary value (write_word_state before address value)

theorem translated_word_read [MemoryPlatform SailRV32.exception]
    {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.translate_and_read_value (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .ok (.Ok (.Physaddr (address.setWidth 34), value)) before :=
  translated_memory_read (Or.inr (Or.inr rfl)) configuration aligned ordinary read

theorem word_page_split (address : BitVec 32) (aligned : address.toNat % 4 = 0) :
    SailRV32.Functions.split_on_page_boundary address 4 = pure (4, 0) :=
  memory_page_split address (Or.inr (Or.inr rfl)) aligned

theorem virtual_address_word_read [MemoryPlatform SailRV32.exception]
    {before : State} {address value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .ok value before) :
    run (SailRV32.Functions.vmem_read_addr (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .ok (.Ok value) before :=
  virtual_address_memory_read (Or.inr (Or.inr rfl)) configuration aligned ordinary read

theorem virtual_address_word_write [MemoryPlatform SailRV32.exception]
    {before : State} {address : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address) (value : BitVec 32) :
    run (SailRV32.Functions.vmem_write_addr (.Virtaddr address) 4 value (.Store .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .ok (.Ok true) (wordWriteState before address.toNat value) :=
  virtual_address_memory_write (Or.inr (Or.inr rfl)) configuration aligned ordinary value (write_word_state before address value)

theorem virtual_word_read [MemoryPlatform SailRV32.exception]
    {before : State} {source value : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % 4 = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (read : (readBytes (ue := SailRV32.exception) 4 (source + offset).toNat).run before =
      .ok value before) :
    run (SailRV32.Functions.vmem_read index offset 4 (.Load .Data) false false false) before =
      .ok (.Ok value) before :=
  virtual_memory_read (Or.inr (Or.inr rfl)) configuration index offset registerRead aligned ordinary read

theorem virtual_word_write [MemoryPlatform SailRV32.exception]
    {before : State} {source : BitVec 32}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % 4 = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (value : BitVec 32) :
    run (SailRV32.Functions.vmem_write index offset 4 value (.Store .Data) false false false) before =
      .ok (.Ok true) (wordWriteState before (source + offset).toNat value) :=
  virtual_memory_write (Or.inr (Or.inr rfl)) configuration index offset registerRead aligned ordinary value (write_word_state before (source + offset) value)

theorem physical_word_read_error {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.mem_read (.Load .Data) .PBMT_PMA .Machine
      (.Physaddr (address.setWidth 34)) 4 false false false) before =
        .error error after :=
  physical_memory_read_error (Or.inr (Or.inr rfl)) configuration aligned ordinary read

theorem translated_word_read_error [MemoryPlatform SailRV32.exception]
    {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.translate_and_read_value (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before =
        .error error after :=
  translated_memory_read_error (Or.inr (Or.inr rfl)) configuration aligned ordinary read

theorem virtual_address_word_read_error [MemoryPlatform SailRV32.exception]
    {before after : State} {address : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (aligned : address.toNat % 4 = 0)
    (ordinary : OrdinaryWordAddress address)
    (read : (readBytes (ue := SailRV32.exception) 4 address.toNat).run before = .error error after) :
    run (SailRV32.Functions.vmem_read_addr (.Virtaddr address) 4 (.Load .Data)
      ⟨.Machine, 0, false⟩ false false false) before = .error error after :=
  virtual_address_memory_read_error (Or.inr (Or.inr rfl)) configuration aligned ordinary read

theorem virtual_word_read_error [MemoryPlatform SailRV32.exception]
    {before after : State} {source : BitVec 32}
    {error : _root_.Sail.Error SailRV32.exception}
    (configuration : FlatMemoryConfiguration before) (index : SailRV32.regidx) (offset : BitVec 32)
    (registerRead : run (SailRV32.Functions.rX_bits index) before = .ok source before)
    (aligned : (source + offset).toNat % 4 = 0) (ordinary : OrdinaryWordAddress (source + offset))
    (read : (readBytes (ue := SailRV32.exception) 4 (source + offset).toNat).run before =
      .error error after) :
    run (SailRV32.Functions.vmem_read index offset 4 (.Load .Data) false false false) before =
      .error error after :=
  virtual_memory_read_error (Or.inr (Or.inr rfl)) configuration index offset registerRead aligned ordinary read

end Airbender.Reference.RiscV.Sail
