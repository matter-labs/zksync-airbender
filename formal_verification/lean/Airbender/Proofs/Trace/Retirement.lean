import Airbender.Proofs.Trace.SailHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail

/-- Native cell updates change GPR/RAM data, never PC or nextPC. This frame
    fact separates the logical memory history from original Sail retirement. -/
theorem cell_write_controls {before after : State} {cell : Cell} {value : BitVec 32}
    (written : run (cell.write value) before = .ok () after) :
    after.regs.get? .PC = before.regs.get? .PC ∧
      after.regs.get? .nextPC = before.regs.get? .nextPC := by
  cases cell with
  | register index =>
    obtain ⟨result, execution, pc, next⟩ := gpr_write_controls (.Regidx index) value before
    have same := (EStateM.Result.ok.inj (execution.symm.trans written)).2
    subst result
    exact ⟨pc, next⟩
  | ram address =>
    have same := (EStateM.Result.ok.inj ((write_word_state before address value).symm.trans written)).2
    subst after
    exact ⟨rfl, rfl⟩

/-- Complete native histories retain the control-register image. Instruction
    stepping introduces the actual PC updates through Sail's own clauses. -/
theorem sail_history_controls {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) :
    after.regs.get? .PC = before.regs.get? .PC ∧
      after.regs.get? .nextPC = before.regs.get? .nextPC := by
  induction history with
  | nil => exact ⟨rfl, rfl⟩
  | cons past cell member address read written ih =>
    have frame := cell_write_controls written
    exact ⟨frame.1.trans ih.1, frame.2.trans ih.2⟩

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

theorem sail_history_pc_read {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after)
    {pc : BitVec 32}
    (read : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before) :
    run (SailRV32.Functions.get_arch_pc ()) after = .ok pc after := by
  apply read_register
  rw [(sail_history_controls history).1]
  exact read_register_iff.mp read

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

/-- The actual two register insertions produced by successful Sail retirement.
    Used only to transport native histories through instruction boundaries. -/
def retiredState (state : State) (pc : BitVec 32) : State :=
  { state with regs := state.regs.insert .nextPC pc |>.insert .PC pc }

theorem retired_state_history {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) (pc : BitVec 32) :
    SailHistory cells events (retiredState before pc) (retiredState after pc) :=
  sail_history_control (sail_history_control history .nextPC (.inr rfl) pc) .PC (.inl rfl) pc

theorem retired_state_pc (state : State) (pc : BitVec 32) :
    run (SailRV32.Functions.get_arch_pc ()) (retiredState state pc) =
      .ok pc (retiredState state pc) := by
  apply read_register
  simp [retiredState]

/-- Repeated instruction retirement keeps only the newest control values;
    GPR, RAM and all other actual Sail state fields stay in the same state. -/
theorem retired_state_overwrite (state : State) (old current : BitVec 32) :
    retiredState (retiredState state old) current = retiredState state current := by
  unfold retiredState
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reader
  by_cases pc : reader = .PC
  · subst reader
    simp
  · by_cases next : reader = .nextPC
    · subst reader
      simp [Std.ExtDHashMap.get?_insert]
    · simp [Std.ExtDHashMap.get?_insert, Ne.symm pc, Ne.symm next]

/-- Sail's own nextPC preparation erases the previous nextPC value. Rebasing
    at an already matching PC therefore preserves every normal instruction. -/
theorem normal_step_rebased {before : State} {pc : BitVec 32}
    (read : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before)
    (clause : SailRV32.SailM SailRV32.ExecutionResult) :
    run (normalStep clause) (retiredState before pc) = run (normalStep clause) before := by
  have actual := read_register_iff.mp read
  have same : { (retiredState before pc) with regs := (retiredState before pc).regs.insert .nextPC (_root_.Sail.BitVec.addInt pc 4) } =
      { before with regs := before.regs.insert .nextPC (_root_.Sail.BitVec.addInt pc 4) } := by
    change { before with regs := ((before.regs.insert .nextPC pc).insert .PC pc).insert .nextPC (_root_.Sail.BitVec.addInt pc 4) } = _
    congr 1
    apply Std.ExtDHashMap.ext_get?
    intro reader
    by_cases current : reader = .PC
    · subst reader
      simp [Std.ExtDHashMap.get?_insert, actual]
    · by_cases next : reader = .nextPC
      · subst reader
        simp
      · simp [Std.ExtDHashMap.get?_insert, Ne.symm current, Ne.symm next]
  simp only [normalStep, SailRV32.Functions.normal_base_next_pc, freeM_bind_assoc]
  have readPC : run (SailRV32.readReg .PC) before = .ok pc before := read
  have rebasedPC : run (SailRV32.readReg .PC) (retiredState before pc) =
      .ok pc (retiredState before pc) := retired_state_pc before pc
  rw [run_bind_of_ok _ _ _ _ _ rebasedPC]
  rw [run_bind_of_ok _ _ _ _ _ readPC]
  rw [run_bind_of_ok _ _ _ _ _ (write_register .nextPC (_root_.Sail.BitVec.addInt pc 4) (retiredState before pc))]
  rw [run_bind_of_ok _ _ _ _ _ (write_register .nextPC (_root_.Sail.BitVec.addInt pc 4) before)]
  rw [same]

theorem matches_control {cells : List Cell} {history : TimestampSortedMemoryAccessList}
    {before : State} (realized : SailStateMatches cells history before)
    (setter : SailRV32.Register) (control : setter = .PC ∨ setter = .nextPC)
    (pc : SailRV32.RegisterType setter) :
    SailStateMatches cells history { before with regs := before.regs.insert setter pc } := by
  intro cell member
  rcases control with rfl | rfl
  · exact cell_read_PC cell (realized cell member) pc
  · exact cell_read_nextPC cell (realized cell member) pc

/-- PC preparation/retirement does not change the public register/RAM image. -/
theorem initial_image_control {cells : List Cell} {tokens : List (MemoryToken p)}
    {before : State} (image : initialImage before cells = some tokens)
    (setter : SailRV32.Register) (control : setter = .PC ∨ setter = .nextPC)
    (pc : SailRV32.RegisterType setter) :
    initialImage { before with regs := before.regs.insert setter pc } cells = some tokens := by
  have reads := image_reads image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, read, rfl⟩ := head
    have mirrored : cell.read { before with regs := before.regs.insert setter pc } =
        .ok value { before with regs := before.regs.insert setter pc } := by
      rcases control with rfl | rfl
      · exact cell_read_PC cell read pc
      · exact cell_read_nextPC cell read pc
    change List.mapM _ (cell :: cells) = _
    rw [List.mapM_cons]
    change Option.bind
      (match cell.read { before with regs := before.regs.insert setter pc } with
        | .ok value _ => some (cell.initialToken value)
        | .error _ _ => none)
      (fun first => Option.bind
        (initialImage { before with regs := before.regs.insert setter pc } cells)
        (fun rest => some (first :: rest))) = _
    rw [mirrored]
    simp only [Option.bind, ih]

theorem retired_state_image {cells : List Cell} {tokens : List (MemoryToken p)}
    {before : State} (image : initialImage before cells = some tokens) (pc : BitVec 32) :
    initialImage (retiredState before pc) cells = some tokens :=
  initial_image_control (initial_image_control image .nextPC (.inr rfl) pc) .PC (.inl rfl) pc

theorem retired_state_configuration {before : State}
    (configuration : FlatMemoryConfiguration before) (pc : BitVec 32) :
    FlatMemoryConfiguration (retiredState before pc) :=
  configuration_pc_write (configuration_next_pc_write configuration pc) pc

/-- An actual native destination write determines the complete projected Sail
    state, including retirement. Shared by register-writing instruction families. -/
theorem projected_step_of_write {before after : State} (rd : BitVec 5) (output : Output)
    (written : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) before =
      .ok () after) :
    run (projectedStep (.Regidx rd) output) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after output.pc.toBitVec) := by
  have prepared := cell_write_control .nextPC (.inr rfl) output.pc.toBitVec
    (.register rd) output.destination.toBitVec written
  change run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) _ = _ at prepared
  simp only [projectedStep, writeResult, freeM_bind_assoc, freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ (write_register .nextPC output.pc.toBitVec before)]
  rw [run_bind_of_ok _ _ _ _ _ prepared]
  rw [run_bind_of_ok _ _ _ _ _ (write_register .PC output.pc.toBitVec
    { after with regs := after.regs.insert .nextPC output.pc.toBitVec })]
  rfl

end Airbender.Trace.Proofs

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail

/-- Shared sequencing of the original normal-path PC preparation, a checked
    instruction clause, and the original tick_pc retirement. -/
theorem normal_step_native {before after : State} {pc : BitVec 32}
    (instruction : SailRV32.SailM SailRV32.ExecutionResult)
    (current : run (SailRV32.Functions.get_arch_pc ()) before = .ok pc before)
    (executed : run instruction { before with regs := before.regs.insert .nextPC (pc + 4) } =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { after with regs := after.regs.insert .nextPC (pc + 4) }) :
    run (normalStep instruction) before = .ok SailRV32.Functions.RETIRE_SUCCESS
      { after with regs := after.regs.insert .nextPC (pc + 4) |>.insert .PC (pc + 4) } := by
  simp only [normalStep]
  rw [run_bind_of_ok _ _ _ _ _ (initialize_next_pc current)]
  rw [run_bind_of_ok _ _ _ _ _ executed]
  rw [run_bind_of_ok _ _ _ _ _ (tick_pc_run (pc := pc + 4) (by simp))]
  rfl

end Airbender.Reference.RiscV.Sail
