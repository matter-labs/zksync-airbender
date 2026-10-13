import Airbender.Review.UnifiedReduced.MixedWindowProjection
import Airbender.Proofs.Trace.WindowCounts
import Airbender.Proofs.UnifiedReduced.WindowProjection

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true

theorem machine_window_count [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (ordered : lower ≤ upper)
    (afterInitial : (timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value) :
    (data.windowMachineRows lower upper).length = (upper - lower) / 4 :=
  native_window_count hp inverse accepted.constraints accepted.states inputs.initialClock inputs.initialAligned
    first last ordered afterInitial beforeTerminal

theorem window_callers_filter [Fact p.Prime] (data : RequestTrace p) (lower upper : Nat) :
    Delegation.Caller.windowCallers data.callers lower upper =
      (data.windowMachineRows lower upper).filter fun row => decide (Selected row.assignment) := by
  simp only [Delegation.Caller.windowCallers, RequestTrace.callers, RequestTrace.windowMachineRows, List.filter_filter]
  apply List.filter_congr
  intro row _
  exact Bool.and_comm _ _

theorem caller_window_schedule [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {data : RequestTrace p} {before : State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value)
    (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length) :
    CallerWindowSchedule data lower upper := by
  have count := machine_window_count hp inverse accepted inputs first last ordered afterInitial beforeTerminal
  have requests := request_windows hp inverse accepted inputs first last positive
  have callers := Delegation.Caller.Proofs.window_call_count requests
  have workerCount : (data.windowMachineRows lower upper).length = (data.workers.windowRows lower upper).length := by
    rw [count]
    omega
  have same : Delegation.Caller.windowCallers data.callers lower upper = data.windowMachineRows lower upper := by
    rw [window_callers_filter]
    apply List.Sublist.eq_of_length List.filter_sublist
    rw [← window_callers_filter, callers, workerCount]
  exact ⟨count, same, workerCount⟩

theorem caller_window_addresses [Fact p.Prime] {data : RequestTrace p} {before : State}
    (schedule : CallerWindowSchedule data lower upper) (requests : RequestBinding data before) :
    ∀ edge ∈ (data.windowMachineRows lower upper).flatMap (fun row => (machinePorts row).toList.map fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port)),
      edge.1.address = (Cell.register 0).addressCode ∧ edge.2.address = (Cell.register 0).addressCode := by
  intro edge member
  obtain ⟨row, present, step⟩ := List.mem_flatMap.mp member
  have caller : row ∈ data.callers := List.mem_of_mem_filter (schedule.rows.symm ▸ present)
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  rw [machine_ports_caller caller] at portMember
  have modes : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
    simpa [architecturalPorts] using portMember
  rcases modes with rfl | rfl
  · exact ⟨(requests.callers row caller).registers.1, (requests.callers row caller).registers.1⟩
  · exact ⟨(requests.callers row caller).registers.2.1, (requests.callers row caller).registers.2.1⟩

theorem caller_window_filtered_tokens [Fact p.Prime] {data : RequestTrace p} {before : State}
    (schedule : CallerWindowSchedule data lower upper) (requests : RequestBinding data before) (written : Bool) :
    (((data.windowSteps lower upper).map fun edge => if written then edge.2 else edge.1).filter
      fun token => token.address != (Cell.register 0).addressCode) =
      ((data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps).map
        (fun edge => if written then edge.2 else edge.1) :=
  Delegation.Caller.Proofs.filtered_architectural_tokens _ _ (caller_window_addresses schedule requests)
    (Delegation.Caller.Proofs.worker_addresses (data := ⟨data.workers.setup, data.workers.windowRows lower upper, [], []⟩)) written

theorem mixed_projected_window [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (afterInitial : (timeOfPair data.machine.initial.timestamp).value ≤ lower)
    (beforeTerminal : upper ≤ (timeOfPair data.machine.terminal.timestamp).value)
    (duration : upper = lower + 4 * (data.workers.windowRows lower upper).length) :
    MixedProjectedWindowExecution data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have schedule := caller_window_schedule size clockInverse accepted.toRequestChecks inputs.publicProgram
    first last positive ordered afterInitial beforeTerminal duration
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have window := mixed_window_execution hp clockInverse rotationInverse accepted inputs first last positive ordered
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm,
    firstHistory, spanHistory, prefixMatching, matching, startBoundary, finishBoundary⟩ := window.execution
  have selectedMatching := matching.filter fun token => token.address != (Cell.register 0).addressCode
  have writes := caller_window_filtered_tokens schedule requests true
  have reads := caller_window_filtered_tokens schedule requests false
  change ((data.windowSteps lower upper).map Prod.snd).filter _ = _ at writes
  change ((data.windowSteps lower upper).map Prod.fst).filter _ = _ at reads
  simp only [List.filter_append, writes, reads] at selectedMatching
  have startProjected := native_boundary_restriction startBoundary
  have finishProjected := native_boundary_restriction finishBoundary
  have spanSteps : (data.windowSteps lower upper).filter (fun edge => edge.1.address != (Cell.register 0).addressCode) =
      (data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps := by
    simp only [RequestTrace.windowSteps, List.filter_append]
    have machineRemoved : ((data.windowMachineRows lower upper).flatMap fun row => (machinePorts row).toList.map fun port =>
        (readToken row.assignment port, writeToken row.columns row.assignment port)).filter
        (fun edge => edge.1.address != (Cell.register 0).addressCode) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro edge member
      simp [(caller_window_addresses schedule requests edge member).1]
    rw [machineRemoved, List.nil_append]
    apply List.filter_eq_self.mpr
    intro edge member
    exact bne_iff_ne.mpr (Delegation.Caller.Proofs.worker_addresses
      (data := ⟨data.workers.setup, data.workers.windowRows lower upper, [], []⟩) edge member).1
  let workerEvents := spanEvents.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)
  have workerPerm : workerEvents.Perm
      (((data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps).map transferEvent) := by
    have actual := spanPerm.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode))
    rw [List.filter_map] at actual
    change workerEvents.Perm (((data.windowSteps lower upper).filter
      fun edge => decide (edge.1.address ≠ (Cell.register 0).addressCode)).map transferEvent) at actual
    have predicate : (fun edge : MemoryToken p × MemoryToken p => decide (edge.1.address ≠ (Cell.register 0).addressCode)) =
        (fun edge => edge.1.address != (Cell.register 0).addressCode) := by
      funext edge
      apply Bool.eq_iff_iff.mpr
      simp
    rw [predicate, spanSteps] at actual
    exact actual
  refine ⟨schedule, window.requests, start, finish, earlierEvents, spanEvents, atStart, atFinish,
    firstPerm, spanPerm, firstHistory, spanHistory, prefixMatching, matching, startBoundary, finishBoundary,
    ⟨?_, selectedMatching⟩, ⟨startProjected.1, inputs.distinct.sublist (List.filter_sublist.map Cell.addressCode),
      fun token member => (startProjected.2 token member).2,
      fun row member => (requests.clocks row (List.mem_of_mem_filter member)).2⟩,
    finishProjected, ⟨⟨workerEvents, workerPerm, history_worker_cells spanHistory⟩, ?_⟩⟩
  · intro row member
    exact accepted.workerConstraints row (List.mem_of_mem_filter member)
  · intro token member
    exact native_boundary_read finishProjected member

end Airbender.UnifiedReduced.Caller.Proofs
