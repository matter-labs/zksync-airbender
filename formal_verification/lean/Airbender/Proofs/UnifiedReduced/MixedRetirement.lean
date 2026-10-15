import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.UnifiedReduced.ArithmeticExecution
import Airbender.Proofs.UnifiedReduced.UnissuedWorkers

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem arithmetic_fields {input : Input} {entry : UnifiedReduced.ProgramEntry}
    (fields : Mixed.decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = arithmeticInstruction input) :
    UnifiedReduced.decoderFields entry.instruction = some entry.data := by
  rcases Mixed.Proofs.fields_cases fields with standard | custom
  · exact standard
  · rw [encoding] at custom
    cases op : input.row.opcode <;> simp [arithmeticInstruction, Sail.instruction, customDecoderFields, op] at custom

theorem ordinary_of_decoder_mask [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {w : Nat → ZMod p} {entry : UnifiedReduced.ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.machine.rom))
    (fields : UnifiedReduced.decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (mask : entry.data.mask.testBit 7 = false) :
    (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers := by
  have flag := UnifiedReduced.Proofs.decoder_selectors hp core
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 query 7
  have disabled : w importedConstraintsDecoderColumns.flags[7] = 0 := by simpa [mask] using flag
  intro member
  have selected := of_decide_eq_true (List.mem_filter.mp member).2
  change w importedConstraintsDecoderColumns.flags[7] = 1 at selected
  exact zero_ne_one (disabled.symm.trans selected)

theorem arithmetic_ordinary [Fact p.Prime] (hp : 524288 < p)
    {data : RequestTrace p} {w : Nat → ZMod p} {input : Input} {entry : UnifiedReduced.ProgramEntry}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints data.machine.rom))
    (fields : UnifiedReduced.decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = arithmeticInstruction input) (query : decoderQuery w = entry.query) :
    (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers := by
  have zero : entry.data.mask.testBit 7 = false := by
    rw [encoding] at fields
    rcases input with ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
      ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, immediate, upper, state⟩
    change BitVec 5 at rs1 rs2 rd
    cases opcode <;> by_cases discarded : rd = (0#5)
    all_goals simp [arithmeticInstruction, Sail.instruction, UnifiedReduced.decoderFields, Trace.decoderFields,
      arithmeticFields, Trace.arithmeticFields, DecoderData.mapFamily, discarded] at fields
    all_goals rw [← fields]
    all_goals simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  exact ordinary_of_decoder_mask hp core fields query zero

theorem ordinary_cycle_context_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ before after,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
      SailHistory cells (events.filter fun event => decide
        (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
      SailHistory cells (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after finalState ∧
      SailHistory cells (rowEvents 1 row).reverse before after ∧
      ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by decide
  have floor := machine_native_clock_positive (by decide) (by decide) accepted
    inputs.publicProgram inputs.initialization member
  have positive : 0 < Delegation.Caller.startClock row := by omega
  have stepClock := machine_clock_facts clockSize (by decide) accepted.toRequestChecks inputs.publicProgram member
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation clockSize (by decide) accepted.toRequestChecks inputs.publicProgram
    effects.requests permutation member positive
  have native := ordinary_cycle_history clockSize (by decide) accepted.toRequestChecks inputs.publicProgram
    member ordinary cycle (order.sublist List.filter_sublist) current
  refine ⟨before, after, past, current, future, native, ?_⟩
  intro port present
  exact (effects.words _ (mixed_machine_member member (by rwa [machine_ports_ordinary member ordinary]))).1

theorem ordinary_cycle_context
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {row : Trace.Row babyBearModulus UnifiedFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ events finalState before after,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      SailHistory cells (events.filter fun event => decide (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
      SailHistory cells (events.filter fun event => decide
        (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
      SailHistory cells (events.filter fun event => decide (Delegation.Caller.finishClock row < event.1)) after finalState ∧
      SailHistory cells (rowEvents 1 row).reverse before after ∧
      ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context_at accepted inputs effects permutation order history member ordinary
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    ⟨events, finalState, before, after, permutation, history, past, current, future, native, ranges⟩) started

theorem mixed_arithmetic_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {w : Nat → ZMod babyBearModulus} {input : Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (registers : ∀ index, input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = arithmeticInstruction input) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Sail.execution input) := by
  obtain ⟨entry, present, query, encoding⟩ := instruction
  have source := run_program_sources inputs.ordinaryProgram entry present
  have fields := arithmetic_fields (input := input) source.fields encoding
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  have ordinary := arithmetic_ordinary (by decide) core fields encoding query
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_cycle_context_at accepted inputs effects permutation order history member ordinary
  have bounds : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded ∧
      (readToken w importedConstraintsMemoryPorts[1]).word.Bounded := by
    constructor
    all_goals apply ranges
    all_goals simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]
  let actualInput : Input := { input with before := retiredState before (Control.initialPC w).toBitVec }
  have pcWord : input.row.pc = Control.initialPC w := congrArg₂ Word.mk words.pcLo words.pcHi
  have pc : run (SailRV32.Functions.get_arch_pc ()) actualInput.before =
      .ok actualInput.row.pc.toBitVec actualInput.before := by
    change run (SailRV32.Functions.get_arch_pc ()) (retiredState before (Control.initialPC w).toBitVec) = _
    rw [show actualInput.row.pc = Control.initialPC w from pcWord]
    exact retired_state_pc before _
  have actualWords : WordMapping actualInput ⟨Control.destination w, Control.finalPC w⟩ w :=
    ⟨words.leftLo, words.leftHi, words.rightLo, words.rightHi, words.immediateLo, words.immediateHi,
      words.pcLo, words.pcHi, words.destinationIndex, words.outputLo, words.outputHi,
      words.finalPCLo, words.finalPCHi⟩
  have spec := UnifiedReduced.Proofs.arithmetic_soundness_from_history (by decide) core (accepted.active _ member)
    (retired_state_image inputs.initialization (Control.initialPC w).toBitVec)
    (retired_state_history past (Control.initialPC w).toBitVec)
    (retired_state_history native (Control.initialPC w).toBitVec)
    (input := actualInput) registers bounds actualWords fields query encoding pc
  have retired := UnifiedReduced.Proofs.arithmetic_register_retirement (by decide) core fields query
    (input := actualInput) encoding 1 native spec
  refine ⟨before, after, past, current, future, ?_⟩
  simpa [Sail.execution, Sail.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, actualInput, Trace.Row.start, Trace.Row.finish, Trace.Row.columns, CircuitLayout.columns,
    PCState.State.word, rawPair, importedConstraintsTraceColumns, Control.initialPC, Control.finalPC] using retired

theorem mixed_arithmetic_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {w : Nat → ZMod babyBearModulus} {input : Input}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w)
    (registers : ∀ index, input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = arithmeticInstruction input) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Sail.execution input) := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  have retired := mixed_arithmetic_cycle_at accepted inputs effects permutation order history member words registers instruction
  exact (fun _ : 0 < (timeOfPair data.machine.initial.timestamp).value =>
    ⟨events, finalState, permutation, history, retired⟩) started

end Airbender.UnifiedReduced.Caller.Proofs
