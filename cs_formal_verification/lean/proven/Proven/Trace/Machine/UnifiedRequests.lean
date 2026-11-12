module
public import Proven.Trace.Machine.Requests
public import Proven.UnifiedReduced.Trace

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
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

end Airbender.Trace.Machine.Proofs
