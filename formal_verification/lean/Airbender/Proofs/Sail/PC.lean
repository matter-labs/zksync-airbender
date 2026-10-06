import Airbender.Review.Sail
import Airbender.Proofs.Sail.RiscV

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- Native sequential register reads, with no replacement state semantics. -/
theorem read_register {reg : SailRV32.Register} {value : SailRV32.RegisterType reg}
    {state : State} (h : state.regs.get? reg = some value) :
    run (SailRV32.readReg reg) state = .ok value state := by
  dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
    FreeM.liftM, interpretInstructionEffect]
  simp [h]

theorem read_register_iff {reg : SailRV32.Register} {value : SailRV32.RegisterType reg}
    {state : State} :
    run (SailRV32.readReg reg) state = .ok value state ↔ state.regs.get? reg = some value := by
  dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects,
    FreeM.liftM, interpretInstructionEffect]
  cases found : state.regs.get? reg
  · change EStateM.Result.error _ state = EStateM.Result.ok value state ↔ none = some value
    simp
  · simp

/-- A nextPC write preserves reads of every other native register. -/
theorem read_register_nextPC {reg : SailRV32.Register} {value : SailRV32.RegisterType reg}
    {state : State} (pc : BitVec 32) (other : reg ≠ .nextPC)
    (h : run (SailRV32.readReg reg) state = .ok value state) :
    run (SailRV32.readReg reg) { state with regs := state.regs.insert .nextPC pc } =
      .ok value { state with regs := state.regs.insert .nextPC pc } := by
  apply read_register
  simpa [Std.ExtDHashMap.get?_insert, Ne.symm other] using read_register_iff.mp h

theorem rX_nextPC (reg : SailRV32.regidx) {value pc : BitVec 32} {state : State}
    (h : run (SailRV32.Functions.rX_bits reg) state = .ok value state) :
    run (SailRV32.Functions.rX_bits reg) { state with regs := state.regs.insert .nextPC pc } =
      .ok value { state with regs := state.regs.insert .nextPC pc } := by
  cases reg with
  | Regidx bits =>
    have hb : bits.toNat < 32 := bits.isLt
    change run (SailRV32.Functions.rX (.Regno (bits.toNat : Int))) state = _ at h
    change run (SailRV32.Functions.rX (.Regno (bits.toNat : Int))) _ = _
    interval_cases bits.toNat
    all_goals first
      | exact read_register_nextPC pc (by decide) h
      | (change EStateM.Result.ok (0 : BitVec 32) state = .ok value state at h
         have hv := (EStateM.Result.ok.inj h).1
         rw [← hv]
         rfl)

/-- Native GPR writes preserve nextPC, including a discarded x0 write. -/
theorem gpr_write_nextPC (rd : SailRV32.regidx) (value : BitVec 32) (state : State) :
    ∃ after, run (SailRV32.Functions.wX_bits rd value) state = .ok () after ∧
      after.regs.get? .nextPC = state.regs.get? .nextPC := by
  have primitive (reg : SailRV32.Register) (v : SailRV32.RegisterType reg) :
      run (do SailRV32.writeReg reg v; pure ()) state =
        .ok () { state with regs := state.regs.insert reg v } := rfl
  have pureRun : run (pure () : SailRV32.SailM Unit) state = .ok () state := rfl
  cases rd with
  | Regidx bits =>
    have hb : bits.toNat < 32 := bits.isLt
    change ∃ after, run (SailRV32.Functions.wX (.Regno (bits.toNat : Int)) value) state = _ ∧ _
    interval_cases bits.toNat <;>
      simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
        write_callback_pure, freeM_pure_bind, primitive, pureRun,
        Std.ExtDHashMap.get?_insert]

theorem writeResult_nextPC {rd : SailRV32.regidx} {output : Airbender.Arithmetic.Word}
    {state after : State} {pc : BitVec 32}
    (before : state.regs.get? .nextPC = some pc)
    (h : run (writeResult rd output) state = .ok SailRV32.Functions.RETIRE_SUCCESS after) :
    after.regs.get? .nextPC = some pc := by
  obtain ⟨written, hw, frame⟩ := gpr_write_nextPC rd output.toBitVec state
  simp only [writeResult] at h
  rw [run_bind_of_ok _ _ _ _ _ hw] at h
  change EStateM.Result.ok _ written = EStateM.Result.ok _ after at h
  rw [← (EStateM.Result.ok.inj h).2]
  exact frame.trans before

theorem write_register (reg : SailRV32.Register) (value : SailRV32.RegisterType reg)
    (state : State) :
    run (SailRV32.writeReg reg value) state =
      .ok () { state with regs := state.regs.insert reg value } := rfl

/-- Initialization generated from the exact assignment in upstream's normal
    F_Base path. Successful PC reading is an input-state interface condition. -/
theorem initialize_next_pc {state : State} {pc : BitVec 32}
    (h : run (SailRV32.Functions.get_arch_pc ()) state = .ok pc state) :
    run (SailRV32.Functions.normal_base_next_pc ()) state =
      .ok () { state with regs := state.regs.insert .nextPC (pc + 4) } := by
  change run (SailRV32.readReg .PC) state = .ok pc state at h
  simp only [SailRV32.Functions.normal_base_next_pc]
  rw [run_bind_of_ok _ _ _ _ _ h]
  exact write_register .nextPC (pc + 4) state

/-- Sail's actual retirement accessor copies nextPC to PC. -/
theorem tick_pc_run {state : State} {pc : BitVec 32}
    (h : state.regs.get? .nextPC = some pc) :
    run (SailRV32.Functions.tick_pc ()) state =
      .ok () { state with regs := state.regs.insert .PC pc } := by
  have next := read_register h
  have current : run (SailRV32.readReg .PC)
      { state with regs := state.regs.insert .PC pc } =
      .ok pc { state with regs := state.regs.insert .PC pc } :=
    read_register (by simp)
  simp only [SailRV32.Functions.tick_pc]
  rw [run_bind_of_ok _ _ _ _ _ next]
  rw [run_bind_of_ok _ _ _ _ _ (write_register .PC pc state)]
  rw [run_bind_of_ok _ _ _ _ _ current]
  rfl

/-- Preparing nextPC preserves the instruction's existing read/encoding contract. -/
theorem contract_nextPC {input : Input} (hc : Contract input) (pc : BitVec 32) :
    Contract { input with before := { input.before with regs := input.before.regs.insert .nextPC pc } } := by
  constructor
  · intro condition
    obtain ⟨value, read, mapping⟩ := hc.leftRead condition
    exact ⟨value, rX_nextPC input.rs1 read, mapping⟩
  · intro condition
    obtain ⟨value, read, mapping⟩ := hc.rightRead condition
    exact ⟨value, rX_nextPC input.rs2 read, mapping⟩
  · exact hc.signExtension
  · exact hc.upperImmediate
  · exact read_register_nextPC pc (by decide) hc.pcRead

/-- Reused retirement rule: circuit-proved PC increment plus destination effect
    equality establishes the shared native-state claim. -/
theorem retire_of_destination {before : State} {initialPC : BitVec 32}
    {instruction : SailRV32.SailM SailRV32.ExecutionResult} {rd : SailRV32.regidx} {output : Output}
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) before = .ok initialPC before)
    (pc : output.pc.toBitVec = initialPC + 4)
    (destination : ∃ written,
      run instruction { before with regs := before.regs.insert .nextPC output.pc.toBitVec } =
        .ok SailRV32.Functions.RETIRE_SUCCESS written ∧
      run (writeResult rd output.destination)
        { before with regs := before.regs.insert .nextPC output.pc.toBitVec } =
        .ok SailRV32.Functions.RETIRE_SUCCESS written) :
    stepSpec before instruction rd output := by
  let prepared : State := { before with regs := before.regs.insert .nextPC output.pc.toBitVec }
  have initialized : run (SailRV32.Functions.normal_base_next_pc ()) before = .ok () prepared := by
    simpa only [prepared, pc] using initialize_next_pc pcRead
  obtain ⟨written, executed, projected⟩ := destination
  have stored : written.regs.get? .nextPC = some output.pc.toBitVec :=
    writeResult_nextPC (by simp) projected
  refine ⟨{ written with regs := written.regs.insert .PC output.pc.toBitVec }, ?_, ?_⟩
  · simp only [normalStep]
    rw [run_bind_of_ok _ _ _ _ _ initialized]
    rw [run_bind_of_ok _ _ _ _ _ executed]
    rw [run_bind_of_ok _ _ _ _ _ (tick_pc_run stored)]
    rfl
  · simp only [projectedStep]
    rw [run_bind_of_ok _ _ _ _ _ (write_register .nextPC output.pc.toBitVec before)]
    rw [run_bind_of_ok _ _ _ _ _ projected]
    rw [run_bind_of_ok _ _ _ _ _ (write_register .PC output.pc.toBitVec written)]
    rfl

/-- The standard branch instantiates the shared retirement proof. -/
theorem step_of_destination {input : Input} {output : Output} (hc : Contract input)
    (pc : output.pc.toBitVec = input.row.pc.toBitVec + 4)
    (destination : ∀ state, Contract { input with before := state } →
      destinationSpec { input with before := state } output.destination) : spec input output := by
  apply retire_of_destination hc.pcRead pc
  exact destination _ (contract_nextPC hc output.pc.toBitVec)

/-- A custom architectural no-op has only the same native PC retirement effects. -/
theorem retire_no_write {before : State} {initialPC : BitVec 32}
    {finalPC : Airbender.Arithmetic.Word}
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) before = .ok initialPC before)
    (pc : finalPC.toBitVec = initialPC + 4) :
    stepSpec before (pure SailRV32.Functions.RETIRE_SUCCESS) zeroRegister ⟨⟨0, 0⟩, finalPC⟩ := by
  apply retire_of_destination pcRead pc
  refine ⟨_, rfl, ?_⟩
  simp only [writeResult, write_zero, freeM_pure_bind]
  rfl

/-- Standard and custom rows compose through the same native-state relation.
    Establishing the state link from execution/memory arguments remains separate. -/
theorem compose_steps {first second : State}
    {firstInstruction secondInstruction : SailRV32.SailM SailRV32.ExecutionResult}
    {firstRd secondRd : SailRV32.regidx} {firstOutput secondOutput : Output}
    (hfirst : stepSpec first firstInstruction firstRd firstOutput)
    (hsecond : stepSpec second secondInstruction secondRd secondOutput)
    (link : ∀ after, run (projectedStep firstRd firstOutput) first =
      .ok SailRV32.Functions.RETIRE_SUCCESS after → second = after) :
    ∃ after,
      run (do let _ ← normalStep firstInstruction; normalStep secondInstruction) first =
        .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      run (do let _ ← projectedStep firstRd firstOutput; projectedStep secondRd secondOutput) first =
        .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  obtain ⟨middle, actualFirst, projectedFirst⟩ := hfirst
  obtain ⟨after, actualSecond, projectedSecond⟩ := hsecond
  have linked := link middle projectedFirst
  refine ⟨after, ?_, ?_⟩
  · rw [run_bind_of_ok _ _ _ _ _ actualFirst, ← linked]
    exact actualSecond
  · rw [run_bind_of_ok _ _ _ _ _ projectedFirst, ← linked]
    exact projectedSecond

theorem compose {first second : Input} {firstOutput secondOutput : Output}
    (hfirst : spec first firstOutput) (hsecond : spec second secondOutput)
    (link : ∀ after, run (projectedStep first.rd firstOutput) first.before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after → second.before = after) :
    ∃ after,
      run (do let _ ← normalStep (execution first); normalStep (execution second)) first.before =
        .ok SailRV32.Functions.RETIRE_SUCCESS after ∧
      run (do let _ ← projectedStep first.rd firstOutput; projectedStep second.rd secondOutput) first.before =
        .ok SailRV32.Functions.RETIRE_SUCCESS after :=
  compose_steps hfirst hsecond link

end Airbender.Reference.RiscV.Sail
