import Airbender.Proofs.Reduced.CycleDispatch
import Airbender.Proofs.Delegation.Atomic

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem cycle_workers_singleton [Fact p.Prime]
    {data : RequestTrace p} {initial : State} (requests : RequestBinding data initial) (schedule : WorkerSchedule data)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    ∃ worker, worker ∈ data.workers.rows ∧ Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment ∧
      data.cycleWorkers row = [worker] := by
  have selected := member
  obtain ⟨worker, matched, _⟩ := schedule.callers row member
  have called := requests.fulfilled.mem_iff.mp (List.mem_map.mpr ⟨row, member, rfl⟩)
  have live := of_decide_eq_true (List.mem_filter.mp called).2
  let issued := data.workers.rows.filter fun other => decide (Delegation.Requests.Live (Delegation.Requests.fulfillment other))
  have unique : (issued.map fun other => (Delegation.Requests.fulfillment other).time).Nodup := by
    simpa only [issued, List.filter_map, RequestTrace.fulfillments, List.map_map, Function.comp_def]
      using requests.invocations.2
  have included : worker ∈ issued := List.mem_filter.mpr
    ⟨matched.1, by rw [matched.2.1]; exact decide_eq_true live⟩
  have filterIssued : (data.workers.rows.filter fun other => decide
      (Delegation.Requests.fulfillment other = Delegation.Requests.caller row.assignment)) =
      (issued.filter fun other => decide (Delegation.Requests.fulfillment other = Delegation.Requests.caller row.assignment)) := by
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
  have filterTime : (issued.filter fun other => decide (Delegation.Requests.fulfillment other = Delegation.Requests.caller row.assignment)) =
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
  rw [RequestTrace.cycleWorkers, if_pos selected, filterIssued, filterTime,
    key_filter_singleton (fun other => (Delegation.Requests.fulfillment other).time) unique included]

theorem caller_cycle_worker_history [Fact p.Prime]
    {data : RequestTrace p} {initial before after : State} {cells : List Cell}
    (requests : RequestBinding data initial) (schedule : WorkerSchedule data) {row : Trace.Row p PooledFamily} (member : row ∈ data.callers)
    {events : List MemoryAccess} (permutation : events.Perm (data.cycleSteps row |>.map transferEvent))
    (history : SailHistory cells events before after) :
    ∃ worker, worker ∈ data.workers.rows ∧ Delegation.Requests.fulfillment worker = Delegation.Requests.caller row.assignment ∧
      (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)).Perm (worker.memorySteps.map transferEvent) ∧
      SailHistory cells (events.filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) before after := by
  obtain ⟨worker, included, same, single⟩ := cycle_workers_singleton requests schedule member
  have callerRemoved : ((machineEvents row).filter fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event present nonzero
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
    have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨ port = AddSub.importedConstraintsMemoryPorts[2] := by
      rw [machine_ports_caller member] at portMember
      simpa [architecturalPorts] using portMember
    have binding := (requests.callers row member).1
    rcases modes with rfl | rfl
    · exact (of_decide_eq_true nonzero) binding.sourceAddress
    · exact (of_decide_eq_true nonzero) binding.destinationAddress
  have workerKept : ((worker.memorySteps.map transferEvent).filter
      fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode)) = worker.memorySteps.map transferEvent := by
    apply List.filter_eq_self.mpr
    intro event present
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp present
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp edgeMember
    exact decide_eq_true (Delegation.Proofs.port_not_zero worker (by simpa using portMember))
  have projection := permutation.filter (fun event => decide (event.2.1 ≠ (Cell.register 0).addressCode))
  have actual : (data.cycleSteps row |>.map transferEvent) = machineEvents row ++ worker.memorySteps.map transferEvent := by
    rw [RequestTrace.cycleSteps, single]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append, List.map_map, Function.comp_def]
    rfl
  rw [actual, List.filter_append, callerRemoved, workerKept, List.nil_append] at projection
  exact ⟨worker, included, same, projection, history_without_zero history⟩


/-- Exact native matching separates the actual addresses of one worker. -/
theorem worker_addresses_distinct
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : StreamMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ data.workers.rows) :
    (worker.memorySteps.map fun edge => edge.1.address).Nodup := by
  have facts := mixed_memory_facts (by decide) (by decide) accepted inputs effects.requests
  have initialized : Transfer.Inputs (mixedData data) initial cells :=
    ⟨inputs.initialization, inputs.distinct⟩
  have rawUnique := Transfer.raw_address_clocks_distinct facts initialized.toBoundaryInputs
  have nativeSub : (data.mixedSteps.map transferEvent).Sublist (Transfer.rawEvents (mixedData data)) :=
    List.sublist_append_right _ _
  have nativeUnique := rawUnique.sublist (nativeSub.map (fun event => (event.1, event.2.1)))
  have rowSub : worker.memorySteps.Sublist data.workers.steps := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Delegation.MemoryData.steps]
      using (List.singleton_sublist.mpr member).flatMap Delegation.Row.memorySteps
  have allSub : worker.memorySteps.Sublist data.mixedSteps :=
    rowSub.trans (List.sublist_append_right _ _)
  have unique := nativeUnique.sublist ((allSub.map transferEvent).map
    (fun event => (event.1, event.2.1)))
  have constant : (worker.memorySteps.map transferEvent).map (fun event => (event.1, event.2.1)) =
      (worker.memorySteps.map fun edge => edge.1.address).map
        (fun address => (workerClock worker, address)) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro edge present
    have time := worker_event_clock (by decide) effects.requests member
      (List.mem_map.mpr ⟨edge, present, rfl⟩)
    simpa only [transferEvent] using congrArg (fun clock => (clock, edge.1.address)) time
  rw [constant] at unique
  exact unique.of_map _


end Airbender.AddSub.Modular.External.Caller.Proofs
