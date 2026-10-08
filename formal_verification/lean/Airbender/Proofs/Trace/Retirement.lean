import Airbender.Proofs.Trace.SailHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Sail's nextPC preparation leaves all tracked native cell reads unchanged. -/
theorem cell_read_nextPC {before : State} (cell : Cell) {value : BitVec 32}
    (read : cell.read before = .ok value before) (pc : BitVec 32) :
    cell.read { before with regs := before.regs.insert .nextPC pc } =
      .ok value { before with regs := before.regs.insert .nextPC pc } := by
  cases cell with
  | register index => exact rX_nextPC (.Regidx index) read
  | ram _ =>
    exact read_word_frame (before := before)
      (after := { before with regs := before.regs.insert .nextPC pc }) rfl read

/-- Sail's PC retirement leaves all tracked native cell reads unchanged. -/
theorem cell_read_PC {before : State} (cell : Cell) {value : BitVec 32}
    (read : cell.read before = .ok value before) (pc : BitVec 32) :
    cell.read { before with regs := before.regs.insert .PC pc } =
      .ok value { before with regs := before.regs.insert .PC pc } := by
  cases cell with
  | register index => exact rX_PC (.Regidx index) read
  | ram _ =>
    exact read_word_frame (before := before)
      (after := { before with regs := before.regs.insert .PC pc }) rfl read

private theorem register_insert_commute (before : State)
    (first second : SailRV32.Register) (a : SailRV32.RegisterType first)
    (b : SailRV32.RegisterType second) (different : first ≠ second) :
    (before.regs.insert first a).insert second b =
      (before.regs.insert second b).insert first a := by
  apply Std.ExtDHashMap.ext_get?
  intro reader
  by_cases one : reader = first
  · subst reader
    simp [Std.ExtDHashMap.get?_insert, Ne.symm different]
  · by_cases two : reader = second
    · subst reader
      simp [Std.ExtDHashMap.get?_insert, different]
    · simp [Std.ExtDHashMap.get?_insert, Ne.symm one, Ne.symm two]

private theorem gpr_write_control {before after : State} (setter : SailRV32.Register)
    (control : setter = .PC ∨ setter = .nextPC) (pc : SailRV32.RegisterType setter)
    (index : BitVec 5) (value : BitVec 32)
    (written : run (SailRV32.Functions.wX_bits (.Regidx index) value) before = .ok () after) :
    run (SailRV32.Functions.wX_bits (.Regidx index) value)
      { before with regs := before.regs.insert setter pc } =
      .ok () { after with regs := after.regs.insert setter pc } := by
  have primitive (reg : SailRV32.Register) (v : SailRV32.RegisterType reg) (state : State) :
      run (do SailRV32.writeReg reg v; pure ()) state =
        .ok () { state with regs := state.regs.insert reg v } := rfl
  have pureRun (state : State) : run (pure () : SailRV32.SailM Unit) state = .ok () state := rfl
  have bound := index.isLt
  change run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) before = _ at written
  change run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) _ = _
  interval_cases index.toNat
  all_goals simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
    write_callback_pure, freeM_pure_bind, primitive, pureRun, EStateM.Result.ok.injEq] at written ⊢
  all_goals subst after
  all_goals first
    | (solve | simp)
    | (refine ⟨?_, rfl, rfl, rfl⟩
       apply register_insert_commute before
       rcases control with rfl | rfl <;> decide)

/-- Actual native cell writes commute with PC preparation/retirement. This
    allows the existing Clean history to be reused through instruction states. -/
theorem cell_write_control {before after : State} (setter : SailRV32.Register)
    (control : setter = .PC ∨ setter = .nextPC) (pc : SailRV32.RegisterType setter)
    (cell : Cell) (value : BitVec 32)
    (written : run (cell.write value) before = .ok () after) :
    run (cell.write value) { before with regs := before.regs.insert setter pc } =
      .ok () { after with regs := after.regs.insert setter pc } := by
  cases cell with
  | register index => exact gpr_write_control setter control pc index value written
  | ram address =>
    have same := (EStateM.Result.ok.inj ((write_word_state before address value).symm.trans written)).2
    subst after
    change run (writeMemory (size := 4) address value) _ = _
    rw [write_word_state]
    rfl

theorem sail_history_control {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    (setter : SailRV32.Register) (control : setter = .PC ∨ setter = .nextPC)
    (pc : SailRV32.RegisterType setter) :
    SailHistory cells events { before with regs := before.regs.insert setter pc }
      { after with regs := after.regs.insert setter pc } := by
  induction history with
  | nil => exact .nil _
  | @cons event rest before middle after past cell member address read written ih =>
    apply SailHistory.cons ih cell member address
    · rcases control with rfl | rfl
      · exact cell_read_PC cell read pc
      · exact cell_read_nextPC cell read pc
    · exact cell_write_control setter control pc cell _ written

theorem matches_control {cells : List Cell} {history : TimestampSortedMemoryAccessList}
    {before : State} (realized : SailStateMatches cells history before)
    (setter : SailRV32.Register) (control : setter = .PC ∨ setter = .nextPC)
    (pc : SailRV32.RegisterType setter) :
    SailStateMatches cells history { before with regs := before.regs.insert setter pc } := by
  intro cell member
  rcases control with rfl | rfl
  · exact cell_read_PC cell (realized cell member) pc
  · exact cell_read_nextPC cell (realized cell member) pc

end Airbender.Trace.Proofs
