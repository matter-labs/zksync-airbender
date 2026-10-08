import Airbender.Proofs.Sail.PC

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- RV32 Machine mode has no pointer masking in the pinned Sail model. -/
theorem machine_pmlen (access : SailRV32.MemoryAccessType SailRV32.mem_payload) :
    SailRV32.Functions.get_pmlen access .Machine = pure 0 := by
  simp [SailRV32.Functions.get_pmlen, SailRV32.Functions.is_pmm_applicable,
    SailRV32.Functions.xlen, freeM_pure_bind]

/-- Zero mstatus disables MPRV, so the actual Sail privilege selection is
    Machine for every ordinary access. These are configuration facts only. -/
theorem machine_effective_privilege (access : SailRV32.MemoryAccessType SailRV32.mem_payload) :
    SailRV32.Functions.effectivePrivilege access 0 .Machine = pure .Machine := by
  simp [SailRV32.Functions.effectivePrivilege, SailRV32.Functions._get_Mstatus_MPRV,
    _root_.Sail.BitVec.extractLsb, BitVec.extractLsb]

/-- The upstream access-info path is discharged from two initialized control
    registers, with no desired address, memory value or transport result premise. -/
theorem machine_access_info {before : State}
    (status : before.regs.get? .mstatus = some 0)
    (privilege : before.regs.get? .cur_privilege = some .Machine)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload) :
    run (SailRV32.Functions.default_access_info access) before =
      .ok ⟨.Machine, 0, false⟩ before := by
  simp only [SailRV32.Functions.default_access_info]
  rw [run_bind_of_ok _ _ _ _ _ (read_register status)]
  rw [run_bind_of_ok _ _ _ _ _ (read_register privilege)]
  rw [machine_effective_privilege, freeM_pure_bind, machine_pmlen, freeM_pure_bind]
  rfl

/-- The generated Machine-mode SATP path still reads misa while evaluating the
    supervisor-extension query. Initialization suffices; no SATP contents are used. -/
theorem machine_satp_mode {before : State} {isa : BitVec 32}
    (initialized : before.regs.get? .misa = some isa) :
    run (SailRV32.Functions.satp_mode .Machine) before = .ok .Bare before := by
  have enabled : run (SailRV32.Functions.currentlyEnabled .Ext_S) before =
      .ok (SailRV32.Functions.hartSupports .Ext_S &&
        ((SailRV32.Functions._get_Misa_S isa == 1#1) &&
          SailRV32.Functions.hartSupports .Ext_Zicsr)) before := by
    simp only [SailRV32.Functions.currentlyEnabled, freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ (read_register initialized)]
    rfl
  simp only [SailRV32.Functions.satp_mode]
  rw [run_bind_of_ok _ _ _ _ _ enabled]
  rfl

private theorem machine_senvcfg {before : State} {supervisor machine : BitVec 64}
    (supervisorConfig : before.regs.get? .senvcfg = some supervisor)
    (machineConfig : before.regs.get? .menvcfg = some machine)
    (privilege : before.regs.get? .cur_privilege = some .Machine) :
    ∃ value, run (SailRV32.Functions.read_senvcfg ()) before = .ok value before := by
  simp only [SailRV32.Functions.read_senvcfg, SailRV32.Functions.inVirtualPrivilege,
    freeM_bind_assoc]
  rw [run_bind_of_ok _ _ _ _ _ (read_register supervisorConfig)]
  rw [run_bind_of_ok _ _ _ _ _ (read_register machineConfig)]
  rw [run_bind_of_ok _ _ _ _ _ (read_register supervisorConfig)]
  rw [run_bind_of_ok _ _ _ _ _ (read_register privilege)]
  exact ⟨_, rfl⟩

/-- The upstream supervisor user-address check is false in Machine mode. Its
    eagerly evaluated environment reads are discharged from initialized CSRs. -/
theorem machine_svukte [MemoryPlatform SailRV32.exception]
    {before : State} {supervisor machine : BitVec 64}
    (supervisorConfig : before.regs.get? .senvcfg = some supervisor)
    (machineConfig : before.regs.get? .menvcfg = some machine)
    (privilege : before.regs.get? .cur_privilege = some .Machine)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload) (mode : SailRV32.SATPMode) :
    run (SailRV32.Functions.is_svukte_qualified access .Machine mode) before =
      .ok false before := by
  obtain ⟨value, read⟩ := machine_senvcfg supervisorConfig machineConfig privilege
  simp only [SailRV32.Functions.is_svukte_qualified, freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ (read_register privilege)]
  simp only [show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl,
    show (SailRV32.Privilege.Machine == .User) = false from rfl,
    Bool.false_and, Bool.false_or, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [run_bind_of_ok _ _ _ _ _ read]
  rfl

/-- Bare Machine translation in the original first-stage address translator. -/
theorem machine_translate_vs [MemoryPlatform SailRV32.exception] {before : State} {isa : BitVec 32}
    (initialized : before.regs.get? .misa = some isa)
    (address : SailRV32.virtaddr)
    (access : SailRV32.MemoryAccessType SailRV32.mem_payload) :
    run (SailRV32.Functions.translate_vs_stage address access .Machine) before =
      .ok (.Ok ((SailRV32.Functions.bits_of_virtaddr address).setWidth 34, .PBMT_PMA, ())) before := by
  simp only [SailRV32.Functions.translate_vs_stage, freeM_pure_bind,
    show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
    show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl,
    Bool.false_or, Bool.false_eq_true, ite_false]
  rw [run_bind_of_ok _ _ _ _ _ (machine_satp_mode initialized)]
  rfl

/-- Ordinary Machine accesses use the original Sail translator with unchanged
    state and the zero-extended virtual address. This establishes translation,
    not PMP/PMA permission or a successful read/write. -/
theorem machine_translate_address [MemoryPlatform SailRV32.exception]
    {before : State} {isa : BitVec 32} {supervisor machine : BitVec 64}
    (initialized : before.regs.get? .misa = some isa)
    (supervisorConfig : before.regs.get? .senvcfg = some supervisor)
    (machineConfig : before.regs.get? .menvcfg = some machine)
    (privilege : before.regs.get? .cur_privilege = some .Machine)
    (address : BitVec 32) (access : SailRV32.MemoryAccessType SailRV32.mem_payload)
    (ordinary : access = .Load .Data ∨ access = .Store .Data ∨ access = .InstructionFetch ()) :
    run (SailRV32.Functions.translateAddr (.Virtaddr address) access .Machine) before =
      .ok (.Ok (.Physaddr (address.setWidth 34), .PBMT_PMA, ())) before := by
  have shadow : SailRV32.Functions.is_shadow_stack_access access = pure false := by
    rcases ordinary with rfl | rfl | rfl <;> rfl
  simp only [SailRV32.Functions.translateAddr,
    show (SailRV32.Privilege.Machine == .VirtualSupervisor) = false from rfl,
    show (SailRV32.Privilege.Machine == .VirtualUser) = false from rfl,
    Bool.false_or, Bool.false_eq_true, ite_false, SailRV32.SailME.run,
    early_return_lift_bind]
  rw [run_bind_of_ok _ _ _ _ _ (machine_satp_mode initialized)]
  simp only [shadow, early_return_lift_bind, freeM_pure_bind,
    Bool.false_eq_true, ite_false]
  rw [run_bind_of_ok _ _ _ _ _
    (machine_svukte supervisorConfig machineConfig privilege access .Bare)]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false, early_return_lift_bind]
  rw [run_bind_of_ok _ _ _ _ _ (machine_translate_vs initialized (.Virtaddr address) access)]
  rfl

end Airbender.Reference.RiscV.Sail
