import Airbender.Proofs.Trace.Retirement

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- GPR/RAM transfers preserve the public ISA, privilege and landing-pad CSR
    data used by Sail's control-flow clauses. -/
theorem cell_write_control_flow_csrs {before after : State} {cell : Cell} {value : BitVec 32}
    (written : run (cell.write value) before = .ok () after) :
    after.regs.get? .misa = before.regs.get? .misa ∧
      after.regs.get? .cur_privilege = before.regs.get? .cur_privilege ∧
      after.regs.get? .mseccfg = before.regs.get? .mseccfg := by
  cases cell with
  | register index =>
    have primitive (reg : SailRV32.Register) (v : SailRV32.RegisterType reg) (state : State) :
        run (do SailRV32.writeReg reg v; pure ()) state =
          .ok () { state with regs := state.regs.insert reg v } := rfl
    have pureRun (state : State) : run (pure () : SailRV32.SailM Unit) state = .ok () state := rfl
    have bound := index.isLt
    change run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) before = _ at written
    interval_cases index.toNat
    all_goals simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
      write_callback_pure, freeM_pure_bind, primitive, pureRun, EStateM.Result.ok.injEq] at written
    all_goals subst after
    all_goals simp [Std.ExtDHashMap.get?_insert]
  | ram address =>
    have same := (EStateM.Result.ok.inj ((write_word_state before address value).symm.trans written)).2
    subst after
    exact ⟨rfl, rfl, rfl⟩

/-- Configuration is transported from the public initial state through complete
    native histories; no per-row CSR initialization is needed. -/
theorem sail_history_control_flow_csrs {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) :
    after.regs.get? .misa = before.regs.get? .misa ∧
      after.regs.get? .cur_privilege = before.regs.get? .cur_privilege ∧
      after.regs.get? .mseccfg = before.regs.get? .mseccfg := by
  induction history with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons past cell member address read written ih =>
    have frame := cell_write_control_flow_csrs written
    exact ⟨frame.1.trans ih.1, frame.2.1.trans ih.2.1, frame.2.2.trans ih.2.2⟩

end Airbender.Trace.Proofs
