import Airbender.Proofs.UnifiedReduced.FullCalls
import Airbender.Proofs.Trace.CycleComposition
import Airbender.Proofs.ExternalBoundary.Requests

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

theorem caller_pc_retirement_raw [Fact p.Prime] {data : RequestTrace p} {initial after : State}
    (requests : RequestBinding data initial) {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers)
    (pc : run (SailRV32.Functions.get_arch_pc ()) after = .ok row.start.word.toBitVec after) :
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) after =
      .ok () (retiredState after row.finish.word.toBitVec) := by
  exact ((requests.callers row member).sail after).2.2 pc

theorem full_cycle_transition [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial finalState : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) (requests : RequestBinding data initial)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers → OrdinaryCycle program cells events initial finalState row)
    (callers : ∀ row ∈ data.callers, FullCallerCycle data initial finalState cells events row)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ data.machine.rows) :
    ∃ before after,
      CutState cells events initial (Delegation.Caller.startClock row) before ∧
      CutState cells events initial (Delegation.Caller.finishClock row) after ∧
      FullStep program data.program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec) ∧
      (run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before →
        FullStep program data.program before (retiredState after row.finish.word.toBitVec)) := by
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
  by_cases caller : row ∈ data.callers
  · obtain ⟨before, after, past, current, _, entry, included, _, pc, source, raw, retired⟩ := callers row caller
    refine ⟨before, after, past, history_prefix_of_window order (by omega) past current,
      Or.inr ⟨entry, included, entry_source_retired_state source _, ?_, retired⟩, ?_⟩
    · rw [← pc]
      exact retired_state_pc before _
    · intro read
      refine Or.inr ⟨entry, included, source, pc ▸ read, after, raw, ?_⟩
      exact caller_pc_retirement_raw requests caller (sail_history_pc_read current read)
  · obtain ⟨entry, included, query, clause, selected, before, after, past, current, _, retired⟩ :=
      ordinary row member caller
    have pcWord : row.start.word = Word.ofBitVec entry.pc := by
      cases row with
      | mk kind w =>
        cases kind
        exact native_query_pc_word (by decide) query
    have pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    have source := cycle_source past (run_program_sources inputs.ordinaryProgram entry included)
      code.ram (code.ordinary entry included) pc
    have step : Mixed.Step program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec) :=
      ⟨entry, included, source, pc ▸ retired_state_pc before _, clause, selected, retired⟩
    exact ⟨before, after, past, history_prefix_of_window order (by
        change (timeOfPair row.start.timestamp).value ≤ (timeOfPair row.finish.timestamp).value
        have advance := clocks.2
        change (timeOfPair row.finish.timestamp).value = (timeOfPair row.start.timestamp).value + 4 at advance
        omega) past current,
      Or.inl step, fun read => Or.inl (step_of_rebased read step)⟩

theorem mixed_event_interval
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program) (inputs : RequestInputs data initial ca)
    (requests : RequestBinding data initial) (ledger : ExternalBoundary.Requests.Binding data)
    {event : MemoryAccess} (member : event ∈ data.mixedSteps.map transferEvent) :
    (timeOfPair data.machine.initial.timestamp).value < event.1 ∧
      event.1 ≤ (timeOfPair data.machine.terminal.timestamp).value := by
  have intervals := state_clock_interval (by decide) (by decide) accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have events : event ∈ data.machine.rows.flatMap machineEvents ++
      data.workers.rows.flatMap (fun worker => worker.memorySteps.map transferEvent) := by
    simp only [RequestTrace.mixedSteps, Delegation.MemoryData.steps, List.map_append, List.map_flatMap,
      List.map_map, Function.comp_def] at member
    exact member
  rcases List.mem_append.mp events with machine | worker
  · obtain ⟨row, included, present⟩ := List.mem_flatMap.mp machine
    obtain ⟨offset, bound, time⟩ := machine_event_time (by decide) (by decide) accepted.toRequestChecks inputs included present
    have interval := intervals row included
    change (timeOfPair data.machine.initial.timestamp).value ≤ Delegation.Caller.startClock row ∧
      Delegation.Caller.startClock row + 4 ≤ (timeOfPair data.machine.terminal.timestamp).value at interval
    omega
  · obtain ⟨worker, included, present⟩ := List.mem_flatMap.mp worker
    obtain ⟨caller, called, _, slot⟩ := ExternalBoundary.Requests.Proofs.covered requests ledger worker included
    have interval := intervals caller (List.mem_of_mem_filter called)
    change (timeOfPair data.machine.initial.timestamp).value ≤ Delegation.Caller.startClock caller ∧
      Delegation.Caller.startClock caller + 4 ≤ (timeOfPair data.machine.terminal.timestamp).value at interval
    have time := worker_event_clock (by decide) requests included present
    have actual : event.1 = Delegation.Caller.startClock caller + 4 := by
      rw [time]
      dsimp only [workerClock]
      rw [slot.invocation]
    omega

theorem full_execution_at [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) (requests : RequestBinding data initial)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok data.machine.initial.word.toBitVec initial)
    (ledger : ExternalBoundary.Requests.Binding data)
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : SailHistory cells events initial finalState)
    (ordinary : ∀ row ∈ data.machine.rows, row ∉ data.callers → OrdinaryCycle program cells events initial finalState row)
    (callers : ∀ row ∈ data.callers, FullCallerCycle data initial finalState cells events row)
    (terminal : ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
      cell.addressCode = token.address ∧ cell.read finalState = .ok token.word.toBitVec finalState) :
    Realizes (FullStep program data.program) data.machine initial cells := by
  obtain ⟨path, head, endPoint, edges, _⟩ := state_path_checks (by decide) (by decide)
    accepted.constraints accepted.states inputs.publicProgram.initialClock inputs.publicProgram.initialAligned
  let point (state : PCState.State babyBearModulus) := ((timeOfPair state.timestamp).value, state.word.toBitVec)
  have initialEmpty : (events.filter fun event => decide
      (event.1 ≤ (timeOfPair data.machine.initial.timestamp).value)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member chosen
    have bound := (mixed_event_interval accepted inputs.publicProgram requests ledger (permutation.mem_iff.mp member)).1
    have selected := of_decide_eq_true chosen
    omega
  have terminalAll : (events.filter fun event => decide
      (event.1 ≤ (timeOfPair data.machine.terminal.timestamp).value)) = events := by
    apply List.filter_eq_self.mpr
    intro event member
    exact decide_eq_true (mixed_event_interval accepted inputs.publicProgram requests ledger (permutation.mem_iff.mp member)).2
  have past : CutState cells events initial (point data.machine.initial).1 initial := by
    unfold CutState
    rw [initialEmpty]
    exact .nil _
  have finish : CutState cells events initial (point data.machine.terminal).1 finalState := by
    unfold CutState
    rw [terminalAll]
    exact history
  have transitions : ∀ edge ∈ (path.map point).zip (path.map point).tail, ∃ one two,
      CutState cells events initial edge.1.1 one ∧ CutState cells events initial edge.2.1 two ∧
      FullStep program data.program (retiredState one edge.1.2) (retiredState two edge.2.2) ∧
      (run (SailRV32.Functions.get_arch_pc ()) one = .ok edge.1.2 one →
        FullStep program data.program one (retiredState two edge.2.2)) := by
    intro edge included
    have mapped : ∀ states : List (PCState.State babyBearModulus), (states.map point).zip (states.map point).tail =
        (states.zip states.tail).map (fun edge => (point edge.1, point edge.2)) := by
      intro states
      induction states with
      | nil => rfl
      | cons a rest ih =>
        cases rest with
        | nil => rfl
        | cons b rest =>
          simpa only [List.map_cons, List.tail_cons, List.zip_cons_cons] using
            congrArg (List.cons (point a, point b)) ih
    rw [mapped path] at included
    obtain ⟨native, member, rfl⟩ := List.mem_map.mp included
    obtain ⟨row, present, equal⟩ := List.mem_map.mp (edges.mem_iff.mp member)
    subst native
    exact full_cycle_transition accepted inputs code requests order ordinary callers present
  have first : (path.map point).head? = some (point data.machine.initial) := by
    simpa using congrArg (Option.map point) head
  have last : (path.map point).getLast? = some (point data.machine.terminal) := by
    simpa using congrArg (Option.map point) endPoint
  obtain ⟨after, execution, view⟩ := compose_cuts first last pc past finish transitions
  refine ⟨after, execution, ?_, ?_⟩
  · rcases view with ⟨rfl, same⟩ | rfl
    · have samePC := congrArg Prod.snd same
      change data.machine.initial.word.toBitVec = data.machine.terminal.word.toBitVec at samePC
      rw [← samePC]
      exact sail_history_pc_read history pc
    · exact retired_state_pc _ _
  · intro token member
    obtain ⟨cell, included, address, read⟩ := terminal token member
    rcases view with ⟨rfl, _⟩ | rfl
    · exact ⟨cell, included, address, read⟩
    · exact ⟨cell, included, address, cell_read_PC cell (cell_read_nextPC cell read _) _⟩

end Airbender.UnifiedReduced.Caller.Proofs
