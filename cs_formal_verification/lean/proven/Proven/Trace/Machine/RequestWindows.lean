module
public import Proven.Trace.Machine.CallerTimes
public import Proven.Trace.Machine.CPUEvents

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A matched worker belongs to the unique cycle that issued its occurrence token. -/
theorem request_event_window {α : Type} (rows callers : List α) (rank : α → Nat)
    (call : α → Requests.Request babyBearModulus) (fulfillments : List (Requests.Request babyBearModulus))
    (unique : (rows.map rank).Nodup) (subset : ∀ row ∈ callers, row ∈ rows)
    (aligned : ∀ row ∈ rows, rank row % 4 = 0)
    (tick : ∀ row ∈ callers, (timeOfPair (call row).time).value = rank row + 1)
    (matching : (callers.map call).Perm fulfillments)
    {row : α} (member : row ∈ rows) {request : Requests.Request babyBearModulus}
    (present : request ∈ fulfillments) {time : Nat}
    (eventTime : time = (timeOfPair request.time).value + 3) :
    (rank row < time ∧ time ≤ rank row + 4) ↔ row ∈ callers ∧ request = call row := by
  obtain ⟨source, called, same⟩ := List.mem_map.mp (matching.mem_iff.mpr present)
  have sourceMember := subset source called
  have current := aligned row member
  have previous := aligned source sourceMember
  have issued := tick source called
  have location : time = rank source + 4 := by rw [eventTime, ← same, issued]
  constructor
  · intro interval
    have clock : rank source = rank row := by omega
    have equal : source = row := List.inj_on_of_nodup_map unique sourceMember member clock
    subst source
    exact ⟨called, same.symm⟩
  · rintro ⟨calledHere, matched⟩
    have issuedHere := tick row calledHere
    rw [eventTime, matched, issuedHere]
    omega

/-- Complete unrolled matching assigns every worker event to its issuing CPU cycle. -/
theorem unrolled_request_window {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {request : Requests.Request babyBearModulus} (present : request ∈ workers.fulfillments)
    {time : Nat} (eventTime : time = (timeOfPair request.time).value + 3) :
    (row.clock < time ∧ time ≤ row.clock + 4) ↔
      row ∈ unrolledCallers trace ∧ request = Requests.caller row.assignment := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1) accepted.constraints accepted.states initial aligned
  apply request_event_window trace.rows (unrolledCallers trace) Row.clock
    (fun source => Requests.caller source.assignment) workers.fulfillments
    (state_clocks_unique (by decide) (by decide) accepted.constraints accepted.states initial aligned)
    (fun _ included => (unrolled_caller_member included).1) ?_
    (fun _ included => unrolled_request_time accepted initial aligned included)
    (unrolled_requests_complete accepted initial aligned) member present eventTime
  intro source included
  simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clocks source included).2

/-- Complete unified matching uses the same occurrence-based cycle partition. -/
theorem unified_request_window {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {row : Trace.Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows)
    {request : Requests.Request babyBearModulus} (present : request ∈ workers.fulfillments)
    {time : Nat} (eventTime : time = (timeOfPair request.time).value + 3) :
    (row.clock < time ∧ time ≤ row.clock + 4) ↔
      row ∈ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)) ∧
        request = UnifiedReduced.Caller.request row.assignment := by
  have clocks := state_clock_inputs (by decide : 2 * timestampBase + 4 < babyBearModulus)
    (by decide : (-3840 : ZMod babyBearModulus) * 524288 = 1) accepted.constraints accepted.states initial aligned
  apply request_event_window trace.rows
    (trace.rows.filter fun source => decide (UnifiedReduced.Caller.Selected source.assignment)) Row.clock
    (fun source => UnifiedReduced.Caller.request source.assignment) workers.fulfillments
    (state_clocks_unique (by decide) (by decide) accepted.constraints accepted.states initial aligned)
    (fun _ included => (List.mem_filter.mp included).1) ?_
    (fun _ included => unified_request_time accepted initial aligned (List.mem_filter.mp included).1)
    (unified_requests_complete accepted initial aligned) member present eventTime
  intro source included
  simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clocks source included).2

end Airbender.Trace.Machine.Proofs
