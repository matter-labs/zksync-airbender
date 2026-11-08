module
public import Slop.Blake2G.SeedCall
public import Slop.Blake2G.CallGroups
public import Slop.Delegation.RVExecution
public import Human.Trace.Workers.Blake2G.RVCall

@[expose] public section

/-! RV twins of `CallGroups.call_scheduled_history` and `StateTrace.call_state_trace`: the G span's RV history grouped
    by call in control order, and the per-call RV states with each call's port observations. RAM cells include the
    shadow RAM below `ROM_END`. -/

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- RV sibling of `BoundaryCallInputs`: the proof-level RV boundary (`RVBoundaryInputs`) and the G span ABI. -/
structure RVBoundaryCallInputs [Fact p.Prime] (data : Delegation.MemoryData p)
    (initial : RV.State) (cells : List Cell) (reduced : Bool) : Prop where
  memory : Delegation.Proofs.RVBoundaryInputs data initial cells
  tables : data.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ data.rows, row.family = .blakeG
  active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1
  controlStart : (Cell.register 12).readRV initial = some (if reduced then 128 else 0)
  calls : data.rows.length = callCount reduced

theorem RVBoundaryCallInputs.toSeed [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} {reduced : Bool} (inputs : RVBoundaryCallInputs data initial cells reduced) :
    SeedCallInputs data cells reduced := by
  refine ⟨inputs.memory.toSeed, inputs.tables, inputs.family, inputs.active, ?_, inputs.calls⟩
  intro token present code
  rw [rv_seed_word inputs.memory present code inputs.controlStart]
  cases reduced <;> rfl

theorem rv_call_scheduled_history [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ascending : List (Delegation.Row p)) (after : RV.State), ascending.Perm data.rows ∧
      ascending.Pairwise (fun a b =>
        (timeOfPair (a.writeToken importedConstraintsMemoryPorts[8]).time).value <
        (timeOfPair (b.writeToken importedConstraintsMemoryPorts[8]).time).value) ∧
      (∀ (i : Nat) (bound : i < ascending.length),
        (readToken (ascending[i]'bound).assignment importedConstraintsMemoryPorts[8]).word = controlAt reduced i ∧
        ((ascending[i]'bound).writeToken importedConstraintsMemoryPorts[8]).word = controlAt reduced (i + 1)) ∧
      (∃ sink ∈ data.terminal, sink.address = (Cell.register 12).addressCode ∧
        sink.word = controlAt reduced data.rows.length) ∧
      GroupedRVHistory cells (fun row => row.memorySteps.map transferEvent) ascending.reverse initial after ∧
      (∀ row ∈ data.rows, Blake2G.spec (Native.input row.assignment) (Native.output row.assignment)) ∧
      ∀ token ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = token.address ∧
        cell.readRV after = some (memoryWord token.value) := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have seed := inputs.toSeed
  have bounds := Delegation.SeedProofs.operation_word_bounds hp inverse accepted seed.memory seed.tables
    (by intro row member other; have := inputs.family row member; simp_all)
    (by intro row member other; have := inputs.family row member; simp_all)
  have selected : ∀ row ∈ data.rows, Blake2G.spec (Native.input row.assignment) (Native.output row.assignment) := by
    intro row member
    have holds := accepted.constraints row member
    have reads := bounds.reads row member
    have family := inputs.family row member
    rcases row with ⟨kind, w⟩
    change kind = .blakeG at family
    subst kind
    simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
    have core := Verification.holds_of_sublist holds (List.sublist_append_left
      (importedConstraints (setupTable Control.controllerRows)) importedConstraintsTimestampLookups)
    exact Native.Proofs.native_effects hp inverse core reads
  obtain ⟨ascending, perm, increasing, controls, sink⟩ := seed_ordered_controls clockBound accepted seed
  obtain ⟨events, after, permutation, eventOrder, history, _, _, terminal⟩ :=
    Delegation.Proofs.rv_native_memory_execution_at_boundary clockBound accepted inputs.memory aligned
  let ordered := ascending.reverse
  have orderedPerm : ordered.Perm data.rows := (List.reverse_perm ascending).trans perm
  let clock := fun row : Delegation.Row p =>
    (timeOfPair (row.writeToken importedConstraintsMemoryPorts[8]).time).value + 1
  have rowOrder : ordered.Pairwise (fun a b => clock b < clock a) := by
    apply List.pairwise_reverse.mpr
    exact increasing.imp (by intro a b less; change _ + 1 < _ + 1; omega)
  have projection : events.Perm (ordered.flatMap fun row => row.memorySteps.map transferEvent) := by
    have rows := List.Perm.flatMap_right (fun row => row.memorySteps.map transferEvent) orderedPerm
    have pooled : data.rows.flatMap (fun row => row.memorySteps.map transferEvent) = data.steps.map transferEvent := by
      simp only [Delegation.MemoryData.steps, List.map_flatMap]
    exact permutation.trans (pooled ▸ rows).symm
  have times : ∀ row ∈ ordered, ∀ event ∈ row.memorySteps.map transferEvent, event.1 = clock row := by
    intro row _ event present
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
    obtain ⟨port, member, rfl⟩ := List.mem_map.mp included
    exact call_event_time row (by simpa using member)
  refine ⟨ascending, after, perm, increasing, controls, sink,
    rv_grouped_history clock _ rowOrder eventOrder projection times history, selected, ?_⟩
  intro token member
  obtain ⟨cell, present, code, read⟩ := terminal token member
  exact ⟨cell, present, code, by simpa only [memoryWord, MemoryToken.word] using read⟩

theorem rv_call_state_trace [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVBoundaryCallInputs data initial cells reduced)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (ascending : List (Delegation.Row p)), ∃ count : ascending.length = data.rows.length,
    ∃ (after : RV.State) (states : List RV.State), ∃ stateCount : states.length = data.rows.length + 1,
      ascending.Perm data.rows ∧ states.head? = some after ∧ states.getLast? = some initial ∧
      Delegation.RVTraceMapping data initial after cells ∧
      ∀ i : Fin data.rows.length,
        let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
        Blake2G.spec (Native.input row.assignment) (Native.output row.assignment) ∧
        (readToken row.assignment importedConstraintsMemoryPorts[8]).word =
          controlAt reduced (data.rows.length - 1 - i.val) ∧
        ((row.writeToken importedConstraintsMemoryPorts[8]).word =
          controlAt reduced (data.rows.length - 1 - i.val + 1)) ∧
        ∃ events : List MemoryAccess, events.Perm (row.memorySteps.map transferEvent) ∧
          RVHistory cells events (states[i.val + 1]'(by omega)) (states[i.val]'(by omega)) ∧
          ∀ port ∈ row.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code row.assignment ∧
            cell.readRV (states[i.val + 1]'(by omega)) = some (memoryWord (port.readCode row.assignment)) ∧
            cell.readRV (states[i.val]'(by omega)) = some (memoryWord (port.writeCode row.assignment)) := by
  obtain ⟨ascending, after, permutation, _, controls, _, history, effects, terminal⟩ :=
    rv_call_scheduled_history hp inverse accepted inputs aligned
  have count := permutation.length_eq
  have reversedPerm := (List.reverse_perm ascending).trans permutation
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨states, stateCount, head, last, ports⟩ :=
    rv_grouped_atomic_boundaries clockBound accepted inputs.memory.toSeed reversedPerm history aligned
  have stateLength : states.length = data.rows.length + 1 := by
    simpa only [List.length_reverse, count] using stateCount
  have trace := rv_grouped_trace_mapping reversedPerm history terminal
  refine ⟨ascending, count, after, states, stateLength, permutation, head, last, trace, ?_⟩
  intro i
  let row := ascending.reverse[i.val]'(by simpa only [List.length_reverse, count] using i.isLt)
  have member : row ∈ data.rows := reversedPerm.mem_iff.mp (List.getElem_mem _)
  have index : row = ascending[data.rows.length - 1 - i.val]'(by omega) := by
    simp only [row, List.getElem_reverse, count]
  have control := controls (data.rows.length - 1 - i.val) (by omega)
  rw [← index] at control
  obtain ⟨events, eventPerm, current, observed⟩ :=
    ports i.val (by simpa only [List.length_reverse, count] using i.isLt)
  exact ⟨effects row member, control.1, control.2, events, eventPerm, current, observed⟩

end Airbender.Blake2G.Proofs
