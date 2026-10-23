import Tests.DynamicCopyLoopNative
import Airbender.Review.Trace.UnifiedReduced.PathExecution

namespace Tests.DynamicCopyLoop
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open Airbender.UnifiedReduced.Caller Airbender.UnifiedReduced.Caller.Proofs
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

private def firstCaller : Row babyBearModulus UnifiedFamily := ⟨.machine, Tests.DynamicCopyLoopNative.machineAssignment 7⟩
private def secondCaller : Row babyBearModulus UnifiedFamily := ⟨.machine, Tests.DynamicCopyLoopNative.machineAssignment 11⟩

private theorem preparation32 : PathCallerPreparation Tests.DynamicCopyLoopNative.data 36 .bigint := by
  refine ⟨?_, ?_, ?_⟩
  · intro row member last
    change row ∈ Tests.DynamicCopyLoopNative.machineRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index
    all_goals first
      | (exfalso; revert last; decide +kernel)
      | exact ⟨Tests.DynamicCopyLoopNative.callerEntry, by simp [Tests.DynamicCopyLoopNative.data, Tests.DynamicCopyLoopNative.callerProgram], by decide +kernel, rfl⟩
  · change 8 ≤ 36
    decide
  · change 36 ≤ 68
    decide

private theorem preparation48 : PathCallerPreparation Tests.DynamicCopyLoopNative.data 52 .bigint := by
  refine ⟨?_, ?_, ?_⟩
  · intro row member last
    change row ∈ Tests.DynamicCopyLoopNative.machineRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index
    all_goals first
      | (exfalso; revert last; decide +kernel)
      | exact ⟨Tests.DynamicCopyLoopNative.callerEntry, by simp [Tests.DynamicCopyLoopNative.data, Tests.DynamicCopyLoopNative.callerProgram], by decide +kernel, rfl⟩
  · change 8 ≤ 52
    decide
  · change 52 ≤ 68
    decide

/-- Different native occurrences of the same actual CSR PC132. Bigint's
separate command theorem below supplies F02; no desired native read is a field. -/
private def plan32 : PathCallPlan Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.ordinaryProgram :=
  ⟨32, .bigint, preparation32, trivial, trivial⟩
private def plan48 : PathCallPlan Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.ordinaryProgram :=
  ⟨48, .bigint, preparation48, trivial, trivial⟩
private def plans : List (PathCallPlan Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.ordinaryProgram) := [plan32, plan48]

private theorem pathInputs : PathCallsInputs Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.before [132]
    [0, 4, 8, 12, 16, 20, 128, 136, 140, 144, 152] Tests.DynamicCopyLoopNative.cells Tests.DynamicCopyLoopProgram.ordinaryProgram plans := by
  refine {
    toProtocolContextInputs := ⟨Tests.DynamicCopyLoopNative.inputs.publicProgram, Tests.DynamicCopyLoopNative.inputs.ordinaryProgram,
      Tests.DynamicCopyLoopNative.inputs.initialization, Tests.DynamicCopyLoopNative.inputs.distinct, Tests.DynamicCopyLoopNative.inputs.aligned, Tests.DynamicCopyLoopNative.inputs.setup, Tests.DynamicCopyLoopNative.inputs.tables⟩
    distinctPlans := ?_
    coverage := ?_ }
  · change ([32, 48] : List Nat).Nodup
    decide
  · intro row member entry included pc
    have same : entry = Tests.DynamicCopyLoopNative.callerEntry := by
      simpa only [Tests.DynamicCopyLoopNative.data, Tests.DynamicCopyLoopNative.callerProgram, List.mem_singleton] using included
    subst entry
    change row ∈ Tests.DynamicCopyLoopNative.machineRows at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index
    all_goals first
      | (exfalso; revert pc; decide +kernel)
      | exact ⟨plan32, by simp [plans], by decide +kernel, rfl⟩
      | exact ⟨plan48, by simp [plans], by decide +kernel, rfl⟩

private theorem retirementProfile : RetirementProfile Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.ordinaryProgram Tests.DynamicCopyLoopProgram.before Tests.DynamicCopyLoopNative.cells := by
  refine {
    code := ⟨fun address member => (Tests.DynamicCopyLoopNative.ram_scope address member).1, ?_, ?_⟩
    registers := ?_
    configuration := Tests.DynamicCopyLoopProgram.configuration
    ordinary := ?_
    landingPadDisabled := ?_
    loads := ?_ }
  · intro entry member
    change entry ∈ Tests.DynamicCopyLoopProgram.ordinaryIndices.map Tests.DynamicCopyLoopProgram.ordinaryEntry at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index <;> decide +kernel
  · intro entry member
    have same : entry = Tests.DynamicCopyLoopNative.callerEntry := by
      simpa only [Tests.DynamicCopyLoopNative.data, Tests.DynamicCopyLoopNative.callerProgram, List.mem_singleton] using member
    subst entry
    change 132 < ROM.limit ∧ 132 % 4 = 0
    decide
  · intro register
    change Cell.register register ∈
      (List.finRange 32).map (fun i => Cell.register (BitVec.ofNat 5 i.val)) ++ _
    apply List.mem_append.mpr
    left
    refine List.mem_map.mpr ⟨⟨register.toNat, register.isLt⟩, List.mem_finRange _, ?_⟩
    simp
  · intro address _
    exact ordinaryWordAddress_airbender address
  · intro _
    exact ⟨0, read_register_iff.mp Tests.DynamicCopyLoopProgram.initial_security, by decide +kernel⟩
  · intro entry member immediate source encoding
    change entry ∈ Tests.DynamicCopyLoopProgram.ordinaryIndices.map Tests.DynamicCopyLoopProgram.ordinaryEntry at member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    fin_cases index <;> cases encoding

/-- Both concrete native controls encode COPY: opcode6, carryfalse, word128.
This proves the existing F02 condition for these workers, not arbitrary controls. -/
private theorem commands : BigintCommands Tests.DynamicCopyLoopNative.data := by
  intro worker member _
  change worker ∈ Tests.DynamicCopyLoopNative.workerRows at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  refine ⟨⟨6, false⟩, ?_⟩
  unfold ExternalBoundary.BigintABI.Binding
  fin_cases index <;> decide +kernel

/-- The public actual-path theorem is applied directly to outright accepted
native assignments, original Sail/JALR profile and proved concrete COPY commands. -/
theorem execution : Realizes (FullStep Tests.DynamicCopyLoopProgram.ordinaryProgram Tests.DynamicCopyLoopNative.data.program) Tests.DynamicCopyLoopNative.data.machine Tests.DynamicCopyLoopProgram.before Tests.DynamicCopyLoopNative.cells :=
  path_execution_soundness Tests.DynamicCopyLoopNative.accepted pathInputs retirementProfile Tests.DynamicCopyLoopProgram.initial_pc commands

private theorem final_address (cell : Cell) : (Tests.DynamicCopyLoopNative.final cell).address = cell.addressCode := by
  cases cell with
  | register register => rfl
  | ram address =>
    simp only [Tests.DynamicCopyLoopNative.final]
    split_ifs <;> rfl

private theorem read_terminal {after : State}
    (terminal : ∀ sink ∈ Tests.DynamicCopyLoopNative.data.machine.terminalMemory, ∃ actual ∈ Tests.DynamicCopyLoopNative.cells,
      actual.addressCode = sink.address ∧ actual.read after = .ok sink.word.toBitVec after)
    (cell : Cell) (member : cell ∈ Tests.DynamicCopyLoopNative.cells) :
    cell.read after = .ok (Tests.DynamicCopyLoopNative.final cell).word.toBitVec after := by
  have sink : Tests.DynamicCopyLoopNative.final cell ∈ Tests.DynamicCopyLoopNative.data.machine.terminalMemory := by
    change Tests.DynamicCopyLoopNative.final cell ∈ Tests.DynamicCopyLoopNative.cells.map Tests.DynamicCopyLoopNative.final
    exact List.mem_map.mpr ⟨cell, member, rfl⟩
  obtain ⟨actual, _, address, read⟩ := terminal (Tests.DynamicCopyLoopNative.final cell) sink
  have same : actual = cell := Trace.Proofs.cell_address_injective (address.trans (final_address cell))
  exact same ▸ read

private theorem destination_member : Cell.ram Tests.DynamicCopyLoopProgram.destinationAddress ∈ Tests.DynamicCopyLoopNative.cells := by decide +kernel
private theorem source_member : Cell.ram Tests.DynamicCopyLoopProgram.sourceAddress ∈ Tests.DynamicCopyLoopNative.cells := by decide +kernel
private theorem link_member : Cell.register 1 ∈ Tests.DynamicCopyLoopNative.cells := by decide +kernel
private theorem counter_member : Cell.register 5 ∈ Tests.DynamicCopyLoopNative.cells := by decide +kernel
private theorem control_member : Cell.register 12 ∈ Tests.DynamicCopyLoopNative.cells := by decide +kernel

/-- TerminalPC156, nonzero destination/source words7, actual JAL link148,
finished loop counter/control0, and all other seven words in both blocks. -/
theorem terminal_values : ∃ after : State,
    Relation.ReflTransGen (FullStep Tests.DynamicCopyLoopProgram.ordinaryProgram Tests.DynamicCopyLoopNative.data.program) Tests.DynamicCopyLoopProgram.before after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok 156 after ∧
    (Cell.ram Tests.DynamicCopyLoopProgram.destinationAddress).read after = .ok 7 after ∧
    (Cell.ram Tests.DynamicCopyLoopProgram.sourceAddress).read after = .ok 7 after ∧
    (Cell.register 1).read after = .ok 148 after ∧
    (Cell.register 5).read after = .ok 0 after ∧
    (Cell.register 12).read after = .ok 0 after ∧
    ∀ index : Fin 8, index.val ≠ 0 →
      (Cell.ram (Tests.DynamicCopyLoopProgram.destinationAddress + 4 * BitVec.ofNat 32 index.val)).read after = .ok 0 after ∧
      (Cell.ram (Tests.DynamicCopyLoopProgram.sourceAddress + 4 * BitVec.ofNat 32 index.val)).read after = .ok 0 after := by
  obtain ⟨after, steps, pc, terminal⟩ := execution
  have destination := read_terminal terminal (.ram Tests.DynamicCopyLoopProgram.destinationAddress) destination_member
  have source := read_terminal terminal (.ram Tests.DynamicCopyLoopProgram.sourceAddress) source_member
  have link := read_terminal terminal (.register 1) link_member
  have counter := read_terminal terminal (.register 5) counter_member
  have control := read_terminal terminal (.register 12) control_member
  have destinationValue : (Tests.DynamicCopyLoopNative.final (.ram Tests.DynamicCopyLoopProgram.destinationAddress)).word.toBitVec = 7 := by decide +kernel
  have sourceValue : (Tests.DynamicCopyLoopNative.final (.ram Tests.DynamicCopyLoopProgram.sourceAddress)).word.toBitVec = 7 := by decide +kernel
  have linkValue : (Tests.DynamicCopyLoopNative.final (.register 1)).word.toBitVec = 148 := by decide +kernel
  have counterValue : (Tests.DynamicCopyLoopNative.final (.register 5)).word.toBitVec = 0 := by decide +kernel
  have controlValue : (Tests.DynamicCopyLoopNative.final (.register 12)).word.toBitVec = 0 := by decide +kernel
  rw [destinationValue] at destination
  rw [sourceValue] at source
  rw [linkValue] at link
  rw [counterValue] at counter
  rw [controlValue] at control
  refine ⟨after, steps, pc, destination, source, link, counter, control, ?_⟩
  intro index nonzero
  have destinationMember : Cell.ram (Tests.DynamicCopyLoopProgram.destinationAddress + 4 * BitVec.ofNat 32 index.val) ∈ Tests.DynamicCopyLoopNative.cells := by
    fin_cases index <;> decide +kernel
  have sourceMember : Cell.ram (Tests.DynamicCopyLoopProgram.sourceAddress + 4 * BitVec.ofNat 32 index.val) ∈ Tests.DynamicCopyLoopNative.cells := by
    fin_cases index <;> decide +kernel
  have destinationRead := read_terminal terminal _ destinationMember
  have sourceRead := read_terminal terminal _ sourceMember
  have destinationZero : (Tests.DynamicCopyLoopNative.final (.ram (Tests.DynamicCopyLoopProgram.destinationAddress + 4 * BitVec.ofNat 32 index.val))).word.toBitVec = 0 := by
    fin_cases index
    all_goals first | exact False.elim (nonzero rfl) | decide +kernel
  have sourceZero : (Tests.DynamicCopyLoopNative.final (.ram (Tests.DynamicCopyLoopProgram.sourceAddress + 4 * BitVec.ofNat 32 index.val))).word.toBitVec = 0 := by
    fin_cases index
    all_goals first | exact False.elim (nonzero rfl) | decide +kernel
  exact ⟨destinationZero ▸ destinationRead, sourceZero ▸ sourceRead⟩

private theorem first_called : firstCaller ∈ Tests.DynamicCopyLoopNative.data.callers := by
  rw [Tests.DynamicCopyLoopNative.callers_exact]
  simp [firstCaller]
private theorem second_called : secondCaller ∈ Tests.DynamicCopyLoopNative.data.callers := by
  rw [Tests.DynamicCopyLoopNative.callers_exact]
  simp [secondCaller]

/-- A complete COPY caller cycle retains explicit raw call and original CSR
retirement witnesses, in the actual shared-history prefix/window/suffix. -/
def CompleteCopyCycle (events : List MemoryAccess) (historyFinal : State)
    (row : Row babyBearModulus UnifiedFamily) : Prop :=
  FullCallerCycle Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.before historyFinal Tests.DynamicCopyLoopNative.cells events row ∧
  ∃ before after : State,
    SailHistory Tests.DynamicCopyLoopNative.cells (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) Tests.DynamicCopyLoopProgram.before before ∧
    SailHistory Tests.DynamicCopyLoopNative.cells (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
    SailHistory Tests.DynamicCopyLoopNative.cells (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after historyFinal ∧
    FullCall .bigint before after ∧
    FullRetirement .bigint (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec)

private theorem explicit_copy_cycle {events : List MemoryAccess} {historyFinal : State}
    {row : Row babyBearModulus UnifiedFamily}
    (cycle : FullCallerCycle Tests.DynamicCopyLoopNative.data Tests.DynamicCopyLoopProgram.before historyFinal Tests.DynamicCopyLoopNative.cells events row) :
    CompleteCopyCycle events historyFinal row := by
  refine ⟨cycle, ?_⟩
  obtain ⟨before, after, past, current, future, entry, member, _, _, _, raw, retired⟩ := cycle
  have same : entry = Tests.DynamicCopyLoopNative.callerEntry := by
    simpa only [Tests.DynamicCopyLoopNative.data, Tests.DynamicCopyLoopNative.callerProgram, List.mem_singleton] using member
  subst entry
  exact ⟨before, after, past, current, future, raw, retired⟩

/-- Both actual occurrences at the same callerPC132 have complete COPY effects
and FullRetirement in ONE derived native event history; no history is an input. -/
theorem both_complete_calls : ∃ events : List MemoryAccess, ∃ historyFinal : State,
    events.Perm (Tests.DynamicCopyLoopNative.data.mixedSteps.map transferEvent) ∧
    events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory Tests.DynamicCopyLoopNative.cells events Tests.DynamicCopyLoopProgram.before historyFinal ∧
    CompleteCopyCycle events historyFinal firstCaller ∧
    CompleteCopyCycle events historyFinal secondCaller := by
  have effects := mixed_memory_effects Tests.DynamicCopyLoopNative.accepted Tests.DynamicCopyLoopNative.inputs
  obtain ⟨events, historyFinal, permutation, order, history, _, _, _⟩ := effects.execution
  have first := path_full_caller_cycle_at Tests.DynamicCopyLoopNative.accepted pathInputs retirementProfile.code commands
    effects permutation order history first_called
  have second := path_full_caller_cycle_at Tests.DynamicCopyLoopNative.accepted pathInputs retirementProfile.code commands
    effects permutation order history second_called
  exact ⟨events, historyFinal, permutation, order, history,
    explicit_copy_cycle first, explicit_copy_cycle second⟩

/-- The two call windows are 32→36 and 48→52, despite sharing their caller PC. -/
theorem actual_occurrence_cuts :
    Delegation.Caller.startClock firstCaller = 32 ∧ Delegation.Caller.finishClock firstCaller = 36 ∧
    Delegation.Caller.startClock secondCaller = 48 ∧ Delegation.Caller.finishClock secondCaller = 52 ∧
    firstCaller.start.word.toBitVec = 132 ∧ secondCaller.start.word.toBitVec = 132 := by
  decide +kernel

/-- Concrete final application: complete actual-path execution/terminal values
and both independent complete COPY retirements, with no desired result premise. -/
theorem complete_regression :
    (∃ after : State,
      Relation.ReflTransGen (FullStep Tests.DynamicCopyLoopProgram.ordinaryProgram Tests.DynamicCopyLoopNative.data.program) Tests.DynamicCopyLoopProgram.before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 156 after ∧
      (Cell.ram Tests.DynamicCopyLoopProgram.destinationAddress).read after = .ok 7 after ∧
      (Cell.ram Tests.DynamicCopyLoopProgram.sourceAddress).read after = .ok 7 after) ∧
    (∃ events : List MemoryAccess, ∃ historyFinal : State,
      events.Perm (Tests.DynamicCopyLoopNative.data.mixedSteps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory Tests.DynamicCopyLoopNative.cells events Tests.DynamicCopyLoopProgram.before historyFinal ∧
      CompleteCopyCycle events historyFinal firstCaller ∧
      CompleteCopyCycle events historyFinal secondCaller) := by
  obtain ⟨after, steps, pc, destination, source, _⟩ := terminal_values
  exact ⟨⟨after, steps, pc, destination, source⟩, both_complete_calls⟩

end Tests.DynamicCopyLoop
