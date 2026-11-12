module
public import Proven.Trace.Machine.Requests
public import Proven.UnifiedReduced.Trace

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true
open Delegation

/-- Initialized unified caller clocks leave one invocation tick and two worker-write ticks. -/
theorem unified_caller_clocks {trace : UnifiedTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ∀ row ∈ trace.rows,
      (timeOfPair (UnifiedReduced.Caller.request row.assignment).time).Bounded ∧
      Requests.Live (UnifiedReduced.Caller.request row.assignment) ∧
      (timeOfPair (UnifiedReduced.Caller.request row.assignment).time).lo + 2 < timestampBase := by
  have clocks := Trace.Proofs.state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  intro row present
  have clock := clocks row present
  exact Delegation.Caller.Proofs.caller_clock (by decide) clock.1 clock.2

/-- Unified request matching accounts for every submitted standard and split worker occurrence. -/
theorem unified_requests_complete {trace : UnifiedTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment).Perm workers.fulfillments := by
  apply matching_permutation accepted.requests
  · intro request present
    obtain ⟨row, member, rfl⟩ := List.mem_map.mp present
    exact (unified_caller_clocks accepted initial aligned row (List.mem_filter.mp member).1).2.1
  · exact worker_fulfillments_live accepted.toWorkersAccepted

/-- Unified caller request times identify distinct native CPU occurrences. -/
theorem unified_request_times_unique {trace : UnifiedTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ((((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment)).map Requests.Request.time).Nodup := by
  have clocks := Trace.Proofs.state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  let rank := fun row : Trace.Row babyBearModulus UnifiedFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have unique := Trace.Proofs.state_clocks_unique (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1)
    accepted.constraints accepted.states initial aligned
  have selected : (((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment))).map rank).Nodup :=
    unique.sublist ((List.filter_sublist).map rank)
  simp only [List.map_map, Function.comp_def]
  apply Requests.Proofs.shifted_times_unique selected
  intro row member
  have clock := clocks row (List.mem_filter.mp member).1
  have one : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [UnifiedReduced.Caller.request, Requests.caller, one, rank, Trace.Row.columns,
    CircuitLayout.columns, decodeTimestamp, timeOfPair, rawPair,
    AddSub.importedConstraintsTraceColumns, UnifiedReduced.importedConstraintsTraceColumns] using
    (Trace.Proofs.write_time (by decide : timestampBase < babyBearModulus)
      (base := rawPair row.assignment row.columns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

/-- Complete unified request matching derives the clocks of both worker pools. -/
theorem unified_worker_clocks {trace : UnifiedTrace babyBearModulus}
    {workers : WorkerPools babyBearModulus} {program : List RVMachineProgramEntry}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    (∀ request ∈ workers.fulfillments, (timeOfPair request.time).Bounded ∧
      (timeOfPair request.time).lo + 2 < timestampBase) ∧
    (workers.fulfillments.map Requests.Request.time).Nodup := by
  have matching := unified_requests_complete accepted initial aligned
  refine ⟨?_, (matching.map Requests.Request.time).nodup_iff.mp
    (unified_request_times_unique accepted initial aligned)⟩
  intro request present
  obtain ⟨row, member, rfl⟩ := List.mem_map.mp (matching.mem_iff.mpr present)
  have clock := unified_caller_clocks accepted initial aligned row (List.mem_filter.mp member).1
  exact ⟨clock.1, clock.2.2⟩

end Airbender.Trace.Machine.Proofs
