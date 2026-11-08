import Slop.UnifiedReduced.RVCaller.MixedCalls
import Slop.UnifiedReduced.RVCaller.HistoryWindow

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

def rv_machineEvents (row : Trace.Row p UnifiedFamily) : List MemoryAccess :=
  (machinePorts row).toList.map fun port =>
    transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port)

theorem rv_machine_clocks_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses) :
    (data.machine.rows.map Delegation.Caller.startClock).Nodup := by
  exact state_clocks_unique hp inverse
    accepted.constraints accepted.states inputs.initialClock inputs.initialAligned

theorem rv_machine_clock_facts [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) :
    Delegation.Caller.startClock row % 4 = 0 ∧
      Delegation.Caller.finishClock row = Delegation.Caller.startClock row + 4 := by
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned row member
  refine ⟨?_, ClockLaws.advance hp inverse data.machine.rom row (accepted.constraints row member) clock.1⟩
  simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using clock.2

theorem rv_machine_event_time [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    {event : MemoryAccess} (present : event ∈ rv_machineEvents row) :
    ∃ offset < 3, event.1 = Delegation.Caller.startClock row + offset + 1 := by
  obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
  have native := rv_machine_port_native row (by simpa using included)
  have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned row member
  have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] :=
    @ClockLaws.offsets UnifiedFamily inferInstance p inferInstance inferInstance row
  have selected : port.clock.offset ∈ row.ports.toList.map (fun port => port.clock.offset) :=
    List.mem_map.mpr ⟨port, by simpa using native, rfl⟩
  rw [offsets] at selected
  have bound : port.clock.offset < 3 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    omega
  have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
    clock.1 clock.2 (by omega : port.clock.offset < 4)).2
  exact ⟨port.clock.offset, bound, by simpa only [transferEvent, Delegation.Caller.startClock, Trace.Row.clock, writeToken, decodeTimestamp, timeOfPair, rawPair] using congrArg (fun n => n + 1) time⟩

theorem rv_machine_event_window [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {row other : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) (included : other ∈ data.machine.rows)
    {event : MemoryAccess} (present : event ∈ rv_machineEvents other) :
    (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row) ↔ other = row := by
  have current := rv_machine_clock_facts hp inverse accepted inputs member
  have previous := rv_machine_clock_facts hp inverse accepted inputs included
  obtain ⟨offset, bound, time⟩ := rv_machine_event_time hp inverse accepted inputs included present
  constructor
  · intro interval
    have same : Delegation.Caller.startClock other = Delegation.Caller.startClock row := by omega
    exact List.inj_on_of_nodup_map (rv_machine_clocks_unique hp inverse accepted inputs) included member same
  · intro same
    subst other
    omega

theorem rv_worker_event_window [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    (requests : RVRequestBinding data before)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (positive : 0 < Delegation.Caller.startClock row)
    {worker : Delegation.Row p} (included : worker ∈ data.workers.rows)
    {event : MemoryAccess} (present : event ∈ worker.memorySteps.map transferEvent) :
    (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row) ↔
      Selected row.assignment ∧ Delegation.Requests.fulfillment worker = request row.assignment := by
  have current := rv_machine_clock_facts hp inverse accepted inputs member
  have time := rv_worker_event_clock (by omega) requests included present
  by_cases live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
  · obtain ⟨caller, called, same, slot⟩ := rv_live_worker_slot requests included live
    have source := rv_machine_clock_facts hp inverse accepted inputs (List.mem_filter.mp called).1
    have location : event.1 = Delegation.Caller.startClock caller + 4 := by
      rw [time]
      dsimp only [rv_workerClock]
      rw [slot.invocation]
    constructor
    · intro interval
      have clock : Delegation.Caller.startClock caller = Delegation.Caller.startClock row := by omega
      have equal : caller = row := List.inj_on_of_nodup_map (rv_machine_clocks_unique hp inverse accepted inputs)
        (List.mem_filter.mp called).1 member clock
      subst caller
      exact ⟨of_decide_eq_true (List.mem_filter.mp called).2, same⟩
    · rintro ⟨selected, matched⟩
      have chosen : row ∈ data.callers := List.mem_filter.mpr ⟨member, decide_eq_true selected⟩
      have unique : (data.callers.map (fun caller => (request caller.assignment).time)).Nodup := by
        simpa only [RVRequestTrace.calls, List.map_map, Function.comp_def] using requests.invocations.1
      have equal : caller = row := List.inj_on_of_nodup_map unique called chosen
        (congrArg Delegation.Requests.Request.time (same.symm.trans matched))
      subst caller
      omega
  · have zero : (Delegation.Requests.fulfillment worker).time = (0, 0) := not_not.mp live
    have early : rv_workerClock worker = 3 := by
      change rawPair worker.assignment worker.columns.invocation = (0, 0) at zero
      change (timeOfPair (rawPair worker.assignment worker.columns.invocation)).value + 3 = 3
      rw [zero]
      norm_num [timeOfPair, Timestamp.value, timestampBase]
    rw [early] at time
    constructor
    · intro interval
      omega
    · rintro ⟨selected, same⟩
      have called : row ∈ data.callers := List.mem_filter.mpr ⟨member, decide_eq_true selected⟩
      have actual := requests.fulfilled.mem_iff.mp (List.mem_map.mpr ⟨row, called, rfl⟩)
      have issued := of_decide_eq_true (List.mem_filter.mp actual).2
      exact False.elim (issued ((congrArg Delegation.Requests.Request.time same).symm.trans zero))

theorem rv_machine_window_group [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) :
    ((data.machine.rows.flatMap rv_machineEvents).filter fun event =>
      decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) = rv_machineEvents row := by
  have selected := key_filter_singleton Delegation.Caller.startClock
    (rv_machine_clocks_unique hp inverse accepted inputs) member
  have filtered : ∀ other ∈ data.machine.rows,
      ((rv_machineEvents other).filter fun event =>
        decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) =
      if decide (Delegation.Caller.startClock other = Delegation.Caller.startClock row) then rv_machineEvents other else [] := by
    intro other included
    by_cases same : Delegation.Caller.startClock other = Delegation.Caller.startClock row
    · have equal := List.inj_on_of_nodup_map (rv_machine_clocks_unique hp inverse accepted inputs) included member same
      subst other
      simp only [decide_true, ite_true]
      apply List.filter_eq_self.mpr
      intro event present
      exact decide_eq_true ((rv_machine_event_window hp inverse accepted inputs member member present).mpr rfl)
    · simp only [same, decide_false, Bool.false_eq_true, ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      have equal := (rv_machine_event_window hp inverse accepted inputs member included present).mp (of_decide_eq_true actual)
      exact same (congrArg Delegation.Caller.startClock equal)
  rw [List.filter_flatMap]
  calc
    _ = data.machine.rows.flatMap (fun other =>
        if decide (Delegation.Caller.startClock other = Delegation.Caller.startClock row) then rv_machineEvents other else []) :=
      List.flatMap_congr filtered
    _ = (data.machine.rows.filter fun other => decide
        (Delegation.Caller.startClock other = Delegation.Caller.startClock row)).flatMap rv_machineEvents :=
      (rv_filter_flatMap _ _ _).symm
    _ = rv_machineEvents row := by rw [selected]; simp

theorem rv_worker_window_group [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    (requests : RVRequestBinding data before)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (positive : 0 < Delegation.Caller.startClock row) :
    ((data.workers.rows.flatMap fun worker => worker.memorySteps.map transferEvent).filter fun event =>
      decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) =
      (data.cycleWorkers row).flatMap (fun worker => worker.memorySteps.map transferEvent) := by
  rw [List.filter_flatMap]
  unfold RVRequestTrace.cycleWorkers
  by_cases selected : Selected row.assignment
  · rw [ite_eq_left selected, rv_filter_flatMap]
    apply List.flatMap_congr
    intro worker included
    by_cases same : Delegation.Requests.fulfillment worker = request row.assignment
    · simp only [same, decide_true, ite_true]
      apply List.filter_eq_self.mpr
      intro event present
      exact decide_eq_true ((rv_worker_event_window hp inverse accepted inputs requests member positive included present).mpr
        ⟨selected, same⟩)
    · simp only [same, decide_false, Bool.false_eq_true, ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      exact same ((rv_worker_event_window hp inverse accepted inputs requests member positive included present).mp
        (of_decide_eq_true actual)).2
  · rw [ite_eq_right selected]
    simp only [List.flatMap_nil]
    have removed : ∀ worker ∈ data.workers.rows,
        ((worker.memorySteps.map transferEvent).filter fun event =>
          decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) = [] := by
      intro worker included
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      exact selected ((rv_worker_event_window hp inverse accepted inputs requests member positive included present).mp
        (of_decide_eq_true actual)).1
    calc
      _ = data.workers.rows.flatMap (fun _ => []) := List.flatMap_congr removed
      _ = [] := by simp

theorem rv_cycle_window_permutation [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    (requests : RVRequestBinding data before)
    {events : List MemoryAccess} (permutation : events.Perm (data.mixedSteps.map transferEvent))
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (positive : 0 < Delegation.Caller.startClock row) :
    (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)).Perm
      (data.cycleSteps row |>.map transferEvent) := by
  have projected := permutation.filter fun event => decide
    (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)
  have split : data.mixedSteps.map transferEvent = data.machine.rows.flatMap rv_machineEvents ++
      data.workers.rows.flatMap (fun worker => worker.memorySteps.map transferEvent) := by
    simp only [RVRequestTrace.mixedSteps, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
      Delegation.MemoryData.steps]
    rfl
  rw [split, List.filter_append, rv_machine_window_group hp inverse accepted inputs member,
    rv_worker_window_group hp inverse accepted inputs requests member positive] at projected
  simpa only [RVRequestTrace.cycleSteps, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, rv_machineEvents] using projected

theorem rv_machine_clock_floor [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) :
    (timeOfPair data.machine.initial.timestamp).value ≤ Delegation.Caller.startClock row := by
  have reaches : ∀ clock : Nat, ∀ row ∈ data.machine.rows,
      Delegation.Caller.startClock row = clock → (timeOfPair data.machine.initial.timestamp).value ≤ clock := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro row member value
      have incoming := accepted.states.mem_iff.mpr (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨row, member, rfl⟩))
      rcases List.mem_cons.mp incoming with initial | earlier
      · have same := congrArg (fun token : PCState.State p => (timeOfPair token.timestamp).value) initial
        change Delegation.Caller.startClock row = (timeOfPair data.machine.initial.timestamp).value at same
        omega
      · obtain ⟨previous, present, same⟩ := List.mem_map.mp earlier
        have clockSame := congrArg (fun token : PCState.State p => (timeOfPair token.timestamp).value) same
        change Delegation.Caller.finishClock previous = Delegation.Caller.startClock row at clockSame
        have advance := (rv_machine_clock_facts hp inverse accepted inputs present).2
        have smaller : Delegation.Caller.startClock previous < clock := by omega
        have reached := ih _ smaller previous present rfl
        omega
  exact reaches _ row member rfl

theorem rv_mixed_cycle_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {initial : RV.State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data initial addresses)
    (requests : RVRequestBinding data initial)
    {events : List MemoryAccess} {after : RV.State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events initial after) :
    0 < (timeOfPair data.machine.initial.timestamp).value →
    ∀ row ∈ data.machine.rows, RVCycleExecution data cells events initial after row := by
  intro initialPositive row member
  have floor := rv_machine_clock_floor hp inverse accepted inputs member
  have positive : 0 < Delegation.Caller.startClock row := lt_of_lt_of_le initialPositive floor
  have clocks := rv_machine_clock_facts hp inverse accepted inputs member
  have bounds : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row := by omega
  obtain ⟨before, finish, split, past, current, future⟩ := rv_history_window ordered history bounds
  exact ⟨events.filter (fun event => decide (event.1 ≤ Delegation.Caller.startClock row)),
    events.filter (fun event => decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)),
    events.filter (fun event => decide (Delegation.Caller.finishClock row < event.1)), before, finish,
    split, rv_cycle_window_permutation hp inverse accepted inputs requests permutation member positive,
    past, current, future⟩

theorem rv_cycle_workers_singleton [Fact p.Prime]
    {data : RVRequestTrace p} {initial : RV.State} (requests : RVRequestBinding data initial)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers) :
    ∃ worker, worker ∈ data.workers.rows ∧ Delegation.Requests.fulfillment worker = request row.assignment ∧
      data.cycleWorkers row = [worker] := by
  have selected := of_decide_eq_true (List.mem_filter.mp member).2
  obtain ⟨worker, matched, _⟩ := requests.workers row member
  have called := requests.fulfilled.mem_iff.mp (List.mem_map.mpr ⟨row, member, rfl⟩)
  have live := of_decide_eq_true (List.mem_filter.mp called).2
  let issued := data.workers.rows.filter fun other => decide (Delegation.Requests.Live (Delegation.Requests.fulfillment other))
  have unique : (issued.map fun other => (Delegation.Requests.fulfillment other).time).Nodup := by
    simpa only [issued, List.filter_map, RVRequestTrace.fulfillments, List.map_map, Function.comp_def]
      using requests.invocations.2
  have included : worker ∈ issued := List.mem_filter.mpr
    ⟨matched.1, by rw [matched.2.1]; exact decide_eq_true live⟩
  have filterIssued : (data.workers.rows.filter fun other => decide
      (Delegation.Requests.fulfillment other = request row.assignment)) =
      (issued.filter fun other => decide (Delegation.Requests.fulfillment other = request row.assignment)) := by
    rw [show issued = data.workers.rows.filter (fun other => decide (Delegation.Requests.Live (Delegation.Requests.fulfillment other))) from rfl,
      List.filter_filter]
    apply List.filter_congr
    intro other _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro equal
      exact ⟨equal, by rw [equal]; exact live⟩
    · exact And.left
  have filterTime : (issued.filter fun other => decide (Delegation.Requests.fulfillment other = request row.assignment)) =
      (issued.filter fun other => decide ((Delegation.Requests.fulfillment other).time =
        (Delegation.Requests.fulfillment worker).time)) := by
    apply List.filter_congr
    intro other present
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro equal
      exact congrArg Delegation.Requests.Request.time (equal.trans matched.2.1.symm)
    · intro equal
      have same := List.inj_on_of_nodup_map unique present included equal
      simpa only [same] using matched.2.1
  refine ⟨worker, matched.1, matched.2.1, ?_⟩
  rw [RVRequestTrace.cycleWorkers, ite_eq_left selected, filterIssued, filterTime,
    key_filter_singleton (fun other => (Delegation.Requests.fulfillment other).time) unique included]

theorem rv_caller_cycle_worker_history [Fact p.Prime]
    {data : RVRequestTrace p} {initial before after : RV.State} {cells : List Cell}
    (requests : RVRequestBinding data initial) {row : Trace.Row p UnifiedFamily} (member : row ∈ data.callers)
    {events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (history : RVHistory cells events before after)
    (zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0) :
    ∃ worker, worker ∈ data.workers.rows ∧ Delegation.Requests.fulfillment worker = request row.assignment ∧
      (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm (worker.memorySteps.map transferEvent) ∧
      RVHistory cells (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  obtain ⟨worker, included, same, single⟩ := rv_cycle_workers_singleton requests member
  have callerRemoved : ((rv_machineEvents row).filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event present nonzero
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
    have modes : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
      rw [rv_machine_ports_caller member] at portMember
      simpa [architecturalPorts] using portMember
    have binding := (requests.callers row member).registers
    rcases modes with rfl | rfl
    · exact (of_decide_eq_true nonzero) binding.1
    · exact (of_decide_eq_true nonzero) binding.2.1
  have workerKept : ((worker.memorySteps.map transferEvent).filter
      fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = worker.memorySteps.map transferEvent := by
    apply List.filter_eq_self.mpr
    intro event present
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp present
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
    exact decide_eq_true (Delegation.Proofs.port_not_zero worker (by simpa using portMember))
  have projection := permutation.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode))
  have actual : (data.cycleSteps row |>.map transferEvent) = rv_machineEvents row ++ worker.memorySteps.map transferEvent := by
    rw [RVRequestTrace.cycleSteps, single]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map, Function.comp_def]
    rfl
  rw [actual, List.filter_append, callerRemoved, workerKept, List.nil_append] at projection
  exact ⟨worker, included, same, projection, rv_history_without_zero history zero⟩

theorem rv_ordinary_cycle_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {initial before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data initial addresses)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers)
    {events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events before after) :
    RVHistory cells (rowEvents 1 row).reverse before after := by
  have selected : ¬ Selected row.assignment := by
    intro chosen
    exact ordinary (List.mem_filter.mpr ⟨member, decide_eq_true chosen⟩)
  have cycle : (data.cycleSteps row |>.map transferEvent) = rowEvents 1 row := by
    simp only [RVRequestTrace.cycleSteps, RVRequestTrace.cycleWorkers, ite_eq_right selected,
      List.flatMap_nil, List.append_nil, rv_machine_ports_ordinary member ordinary, List.map_map, Function.comp_def]
    change row.ports.toList.map _ = row.ports.toList.map _
    apply List.map_congr_left
    intro port present
    have native : port ∈ row.ports := by simpa using present
    have clock := state_clock_inputs hp inverse accepted.constraints accepted.states
      inputs.initialClock inputs.initialAligned row member
    have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
      clock.1 clock.2 (Trace.Proofs.port_offset row port native)).2
    change transferEvent (readToken row.assignment port, writeToken row.columns row.assignment port) =
      ((1 + (port.event row.columns row.assignment).1, port.address.code row.assignment,
        port.readCode row.assignment, port.writeCode row.assignment) : MemoryAccess)
    simp only [transferEvent, readToken, writeToken, MemoryPort.event, decodeTimestamp, timeOfPair, rawPair]
    simp only [timeOfPair, rawPair] at time
    rw [time]
    congr 1
    omega
  have target : (rowEvents 1 row).reverse.Pairwise (fun a b => b.1 < a.1) := by
    have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2] :=
      @ClockLaws.offsets UnifiedFamily inferInstance p inferInstance inferInstance row
    have descending : (row.ports.toList.reverse.map fun port => port.clock.offset).Pairwise
        (fun a b : Nat => b < a) := by rw [List.map_reverse, offsets]; decide
    have ports : row.ports.toList.reverse.Pairwise (fun a b => b.clock.offset < a.clock.offset) :=
      List.pairwise_map.mp descending
    change (row.ports.toList.map _).reverse.Pairwise _
    rw [← List.map_reverse]
    apply List.pairwise_map.mpr
    apply ports.imp
    intro a b less
    change 1 + ((decodeTimestamp row.assignment row.columns.initialTime).value + b.clock.offset) <
      1 + ((decodeTimestamp row.assignment row.columns.initialTime).value + a.clock.offset)
    omega
  have projected : events.Perm (rowEvents 1 row).reverse :=
    (cycle ▸ permutation).trans (List.reverse_perm _).symm
  have targetUnique : ((rowEvents 1 row).reverse.map (fun event => event.1)).Nodup :=
    List.pairwise_map.mpr (target.imp (by intro a b less; omega))
  have unique := (projected.map (fun event => event.1)).nodup_iff.mpr targetUnique
  have current : events.Pairwise (fun a b => b.1 < a.1) := (ordered.and (List.pairwise_map.mp unique)).imp (by
    intro a b both
    omega)
  have equal := List.Perm.eq_of_pairwise' target current projected.symm
  exact equal.symm ▸ history

end Airbender.UnifiedReduced.Caller.Proofs
