import Airbender.Review.Helpers.Delegation.StreamCycles
import Airbender.Proofs.Reduced.NativeClocks
import Airbender.Proofs.Delegation.Schedule
import Airbender.Proofs.Trace.MemoryPaths

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def workerClock (worker : Delegation.Row p) :=
  (decodeTimestamp worker.assignment worker.columns.invocation).value + 3

theorem worker_event_clock [Fact p.Prime] (hp : FieldCapacity.NoWrap p timestampBase)
    {data : RequestTrace p} {before : State} (requests : RequestBinding data before)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    {event : MemoryAccess} (present : event ∈ worker.memorySteps.map transferEvent) :
    event.1 = workerClock worker := by
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp included
  have native : port ∈ worker.ports := by simpa using portMember
  have time := (write_time_of_room hp (base := rawPair worker.assignment worker.columns.invocation)
    (offset := port.clock.offset) (requests.clocks worker member) (by
      simpa only [Delegation.Proofs.port_offset worker native, decodeTimestamp, rawPair]
        using (requests.clockRoom worker member))).2
  change (timeOfPair (worker.writeToken port).time).value =
    (decodeTimestamp worker.assignment worker.columns.invocation).value + port.clock.offset at time
  simp only [transferEvent, time, Delegation.Proofs.port_offset worker native, workerClock]

theorem live_worker_slot [Fact p.Prime]
    {data : RequestTrace p} (schedule : WorkerSchedule data)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)) :
    ∃ caller ∈ data.callers,
      Delegation.Requests.fulfillment worker = Delegation.Requests.caller caller.assignment ∧
      Delegation.Caller.WorkerSlot caller worker := by
  obtain ⟨caller, ⟨included, matched, slot⟩, _⟩ := schedule.workers worker member live
  exact ⟨caller, included, matched, slot⟩

theorem worker_event_window [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) (schedule : WorkerSchedule data)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    (positive : 0 < Delegation.Caller.startClock row)
    {worker : Delegation.Row p} (included : worker ∈ data.workers.rows)
    {event : MemoryAccess} (present : event ∈ worker.memorySteps.map transferEvent) :
    (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row) ↔
      row ∈ data.callers ∧ Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment := by
  have current := machine_clock_facts hp inverse accepted inputs member
  have time := worker_event_clock (by omega) requests included present
  by_cases live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
  · obtain ⟨caller, called, same, slot⟩ := live_worker_slot schedule included live
    have source := machine_clock_facts hp inverse accepted inputs (List.mem_filter.mp called).1
    have location : event.1 = Delegation.Caller.startClock caller + 4 := by
      rw [time]
      dsimp only [workerClock]
      rw [slot.invocation]
    constructor
    · intro interval
      have clock : Delegation.Caller.startClock caller = Delegation.Caller.startClock row := by omega
      have equal : caller = row := List.inj_on_of_nodup_map (machine_clocks_unique hp inverse accepted inputs)
        (List.mem_filter.mp called).1 member clock
      subst caller
      exact ⟨called, same⟩
    · rintro ⟨selected, matched⟩
      have chosen : row ∈ data.callers := selected
      have unique : (data.callers.map (fun caller => (Delegation.Requests.caller caller.assignment).time)).Nodup := by
        simpa only [RequestTrace.calls, List.map_map, Function.comp_def] using requests.invocations.1
      have equal : caller = row := List.inj_on_of_nodup_map unique called chosen
        (congrArg Delegation.Requests.Request.time (same.symm.trans matched))
      subst caller
      omega
  · have zero : (Delegation.Requests.fulfillment worker).time = (0, 0) := not_not.mp live
    have early : workerClock worker = 3 := by
      change rawPair worker.assignment worker.columns.invocation = (0, 0) at zero
      change (timeOfPair (rawPair worker.assignment worker.columns.invocation)).value + 3 = 3
      rw [zero]
      norm_num [timeOfPair, Timestamp.value, timestampBase]
    rw [early] at time
    constructor
    · intro interval
      omega
    · rintro ⟨selected, same⟩
      have called : row ∈ data.callers := selected
      have actual := requests.fulfilled.mem_iff.mp (List.mem_map.mpr ⟨row, called, rfl⟩)
      have issued := of_decide_eq_true (List.mem_filter.mp actual).2
      exact False.elim (issued ((congrArg Delegation.Requests.Request.time same).symm.trans zero))

private theorem filter_flatMap (rows : List α) (predicate : α → Bool) (f : α → List β) :
    (rows.filter predicate).flatMap f = rows.flatMap (fun row => if predicate row then f row else []) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => cases result : predicate row <;> simp [result, ih]

theorem machine_window_group [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) :
    ((data.machine.rows.flatMap machineEvents).filter fun event =>
      decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) = machineEvents row := by
  have selected := key_filter_singleton Delegation.Caller.startClock
    (machine_clocks_unique hp inverse accepted inputs) member
  have filtered : ∀ other ∈ data.machine.rows,
      ((machineEvents other).filter fun event =>
        decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) =
      if decide (Delegation.Caller.startClock other = Delegation.Caller.startClock row) then machineEvents other else [] := by
    intro other included
    by_cases same : Delegation.Caller.startClock other = Delegation.Caller.startClock row
    · have equal := List.inj_on_of_nodup_map (machine_clocks_unique hp inverse accepted inputs) included member same
      subst other
      simp only [decide_true, if_true]
      apply List.filter_eq_self.mpr
      intro event present
      exact decide_eq_true ((machine_event_window hp inverse accepted inputs member member present).mpr rfl)
    · simp only [same, decide_false, Bool.false_eq_true, if_false]
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      have equal := (machine_event_window hp inverse accepted inputs member included present).mp (of_decide_eq_true actual)
      exact same (congrArg Delegation.Caller.startClock equal)
  rw [List.filter_flatMap]
  calc
    _ = data.machine.rows.flatMap (fun other =>
        if decide (Delegation.Caller.startClock other = Delegation.Caller.startClock row) then machineEvents other else []) :=
      List.flatMap_congr filtered
    _ = (data.machine.rows.filter fun other => decide
        (Delegation.Caller.startClock other = Delegation.Caller.startClock row)).flatMap machineEvents :=
      (filter_flatMap _ _ _).symm
    _ = machineEvents row := by rw [selected]; simp

theorem worker_window_group [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) (schedule : WorkerSchedule data)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    (positive : 0 < Delegation.Caller.startClock row) :
    ((data.workers.rows.flatMap fun worker => worker.memorySteps.map transferEvent).filter fun event =>
      decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) =
      (data.cycleWorkers row).flatMap (fun worker => worker.memorySteps.map transferEvent) := by
  rw [List.filter_flatMap]
  unfold RequestTrace.cycleWorkers
  by_cases selected : row ∈ data.callers
  · rw [if_pos selected, filter_flatMap]
    apply List.flatMap_congr
    intro worker included
    by_cases same : Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment
    · simp only [same, decide_true, if_true]
      apply List.filter_eq_self.mpr
      intro event present
      exact decide_eq_true ((worker_event_window hp inverse accepted inputs requests schedule member positive included present).mpr
        ⟨selected, same⟩)
    · simp only [same, decide_false, Bool.false_eq_true, if_false]
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      exact same ((worker_event_window hp inverse accepted inputs requests schedule member positive included present).mp
        (of_decide_eq_true actual)).2
  · rw [if_neg selected]
    simp only [List.flatMap_nil]
    have removed : ∀ worker ∈ data.workers.rows,
        ((worker.memorySteps.map transferEvent).filter fun event =>
          decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)) = [] := by
      intro worker included
      apply List.filter_eq_nil_iff.mpr
      intro event present actual
      exact selected ((worker_event_window hp inverse accepted inputs requests schedule member positive included present).mp
        (of_decide_eq_true actual)).1
    calc
      _ = data.workers.rows.flatMap (fun _ => []) := List.flatMap_congr removed
      _ = [] := by simp

theorem cycle_window_permutation [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) (schedule : WorkerSchedule data)
    {events : List MemoryAccess} (permutation : events.Perm (data.mixedSteps.map transferEvent))
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows)
    (positive : 0 < Delegation.Caller.startClock row) :
    (events.filter fun event => decide
      (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)).Perm
      (data.cycleSteps row |>.map transferEvent) := by
  have projected := permutation.filter fun event => decide
    (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)
  have split : data.mixedSteps.map transferEvent = data.machine.rows.flatMap machineEvents ++
      data.workers.rows.flatMap (fun worker => worker.memorySteps.map transferEvent) := by
    simp only [RequestTrace.mixedSteps, List.map_append, List.map_flatMap, List.map_map, Function.comp_def,
      Delegation.MemoryData.steps]
    rfl
  rw [split, List.filter_append, machine_window_group hp inverse accepted inputs member,
    worker_window_group hp inverse accepted inputs requests schedule member positive] at projected
  simpa only [RequestTrace.cycleSteps, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, machineEvents] using projected


theorem machine_clock_floor [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) :
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
        have advance := (machine_clock_facts hp inverse accepted inputs present).2
        have smaller : Delegation.Caller.startClock previous < clock := by omega
        have reached := ih _ smaller previous present rfl
        omega
  exact reaches _ row member rfl

theorem mixed_cycle_execution [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {initial : State} {addresses : List (BitVec 32)} {cells : List Cell}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial addresses)
    (requests : RequestBinding data initial) (schedule : WorkerSchedule data)
    {events : List MemoryAccess} {after : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : SailHistory cells events initial after) :
    0 < (timeOfPair data.machine.initial.timestamp).value →
    ∀ row ∈ data.machine.rows, CycleExecution data cells events initial after row := by
  intro initialPositive row member
  have floor := machine_clock_floor hp inverse accepted inputs member
  have positive : 0 < Delegation.Caller.startClock row := lt_of_lt_of_le initialPositive floor
  have clocks := machine_clock_facts hp inverse accepted inputs member
  have bounds : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row := by omega
  obtain ⟨before, finish, split, past, current, future⟩ := history_window ordered history bounds
  exact ⟨events.filter (fun event => decide (event.1 ≤ Delegation.Caller.startClock row)),
    events.filter (fun event => decide (Delegation.Caller.startClock row < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock row)),
    events.filter (fun event => decide (Delegation.Caller.finishClock row < event.1)), before, finish,
    split, cycle_window_permutation hp inverse accepted inputs requests schedule permutation member positive,
    past, current, future⟩


theorem ordinary_cycle_history [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {initial before after : State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data initial addresses)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers)
    {events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : SailHistory cells events before after) :
    SailHistory cells (rowEvents 1 row).reverse before after := by
  have selected : row ∉ data.callers := ordinary
  have cycle : (data.cycleSteps row |>.map transferEvent) = rowEvents 1 row := by
    simp only [RequestTrace.cycleSteps, RequestTrace.cycleWorkers, if_neg selected,
      List.flatMap_nil, List.append_nil, machine_ports_ordinary member ordinary, List.map_map, Function.comp_def]
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
      @ClockLaws.offsets PooledFamily inferInstance p inferInstance inferInstance row
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

end Airbender.AddSub.Modular.External.Caller.Proofs
