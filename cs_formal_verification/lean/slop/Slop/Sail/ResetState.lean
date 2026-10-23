import Slop.Sail.ResetRun

/-! A concrete `Configured` state for fixtures: every register at its reset value (`resetMap`), with
`configured_reset_map`. Fixtures insert program registers (x1..x31, PC) and memory on top of it; the
decoder on it is decided on the reset state (`decode_configured`). -/

namespace Airbender.Reference.RiscV.Sail
open Configuration

set_option maxRecDepth 100000

/-- Every Sail register of the generated model (`SailRV32.Register`, in declaration order). -/
def allRegisters : List SailRV32.Register :=
  [.hart_state, .ssp, .srmcfg, .vsatp, .satp, .hgatp, .tlb, .pma_regions, .htif_payload_writes, 
    .htif_cmd_write, .htif_exit_code, .htif_done, .htif_tohost, .htif_tohost_base, .pc_reset_address, 
    .elp, .mcontext, .scontext, .tcontrol, .written_trigger_index, .tselect, .triggers, .minstretcfg, 
    .mcyclecfg, .vcsr, .vr31, .vr30, .vr29, .vr28, .vr27, .vr26, .vr25, .vr24, .vr23, .vr22, .vr21, 
    .vr20, .vr19, .vr18, .vr17, .vr16, .vr15, .vr14, .vr13, .vr12, .vr11, .vr10, .vr9, .vr8, .vr7, 
    .vr6, .vr5, .vr4, .vr3, .vr2, .vr1, .vr0, .fcsr, .f31, .f30, .f29, .f28, .f27, .f26, .f25, .f24, 
    .f23, .f22, .f21, .f20, .f19, .f18, .f17, .f16, .f15, .f14, .f13, .f12, .f11, .f10, .f9, .f8, .f7, 
    .f6, .f5, .f4, .f3, .f2, .f1, .f0, .pmpaddr_n, .pmpcfg_n, .written_event_index, .mhpmcounter, 
    .mhpmevent, .vsip, .vsie, .hideleg, .hedeleg, .sig_msip, .msip, .mtime, .mtimecmp, .sig_ssip, 
    .sig_seip, .sig_meip, .mideleg, .medeleg, .mip, .mie, .hvip, .sig_hgeip, .hgeie, .vstimecmp, 
    .stimecmp, .stval, .scause, .sepc, .sscratch, .stvec, .vstval, .vscause, .vsepc, .vsscratch, 
    .vstvec, .htinst, .htval, .htimedelta, .mtval2, .mtinst, .mconfigptr, .mhartid, .marchid, .mimpid, 
    .mvendorid, .minstret_increment, .minstret, .mcycle, .mcountinhibit, .mcounteren, .hcounteren, 
    .scounteren, .mscratch, .mtval, .mepc, .mcause, .mtvec, .hstatus, .cur_inst, .x31, .x30, .x29, 
    .x28, .x27, .x26, .x25, .x24, .x23, .x22, .x21, .x20, .x19, .x18, .x17, .x16, .x15, .x14, .x13, 
    .x12, .x11, .x10, .x9, .x8, .x7, .x6, .x5, .x4, .x3, .x2, .x1, .nextPC, .PC, .vstart, .vl, .vtype, 
    .henvcfg, .menvcfg, .mseccfg, .senvcfg, .sstateen3, .sstateen2, .sstateen1, .sstateen0, .mstateen3, 
    .mstateen2, .mstateen1, .mstateen0, .hstateen3, .hstateen2, .hstateen1, .hstateen0, .vsstatus, 
    .mstatus, .misa, .cur_privilege, .rvfi_mem_data_present, .rvfi_mem_data, .rvfi_int_data_present, 
    .rvfi_int_data, .rvfi_pc_data, .rvfi_inst_data, .rvfi_instruction, .fp_rounding_global]

theorem mem_allRegisters (r : SailRV32.Register) : r ∈ allRegisters := by
  cases r <;> decide

/-- Insert each listed register with its reset value. -/
noncomputable def insertReset (m : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType) :
    List SailRV32.Register → Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType
  | [] => m
  | r :: rest => insertReset (m.insert r (resetState.regs r)) rest

theorem insertReset_get_of_not_mem {r : SailRV32.Register} :
    ∀ (l : List SailRV32.Register) (m : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType),
      r ∉ l → (insertReset m l).get? r = m.get? r
  | [], _, _ => rfl
  | k :: rest, m, outside => by
    simp only [List.mem_cons, not_or] at outside
    rw [insertReset, insertReset_get_of_not_mem rest _ outside.2, Std.ExtDHashMap.get?_insert]
    simp [Ne.symm outside.1]

theorem insertReset_get {r : SailRV32.Register} :
    ∀ (l : List SailRV32.Register) (m : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType),
      r ∈ l → (insertReset m l).get? r = some (resetState.regs r)
  | [], _, member => by cases member
  | k :: rest, m, member => by
    by_cases inside : r ∈ rest
    · exact insertReset_get rest _ inside
    · have same : k = r := by
        rcases List.mem_cons.mp member with equal | equal
        · exact equal.symm
        · exact absurd equal inside
      subst same
      rw [insertReset, insertReset_get_of_not_mem rest _ inside, Std.ExtDHashMap.get?_insert_self]

/-- Every register at its reset value; memory empty. -/
noncomputable def resetMap : State :=
  { (default : State) with regs := insertReset (Std.ExtDHashMap.emptyWithCapacity) allRegisters }

theorem configured_reset_map : Configured resetMap :=
  fun r _ => insertReset_get allRegisters _ (mem_allRegisters r)

/-- Inserting a register a program writes keeps a state `Configured`. -/
theorem Configured.insert {state : State} (configured : Configured state) {key : SailRV32.Register}
    (written : writtenByProgram key = true) (value : SailRV32.RegisterType key) :
    Configured { state with regs := state.regs.insert key value } := by
  intro r outside
  have distinct : key ≠ r := by
    rintro rfl
    rw [written] at outside
    cases outside
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, distinct, ↓reduceDIte]
  exact configured r outside

/-- Memory does not affect `Configured`. -/
theorem Configured.with_mem {state : State} (configured : Configured state)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Configured { state with mem := mem } := configured

end Airbender.Reference.RiscV.Sail
