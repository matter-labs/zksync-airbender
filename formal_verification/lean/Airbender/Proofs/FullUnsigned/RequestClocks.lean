import Airbender.Proofs.FullUnsigned.Requests

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- State matching makes all caller clocks unique. The caller set includes
standard and split requests from the same native CPU trace. -/
theorem unrolled_request_times_unique
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ((pooledCalls trace).map Delegation.Requests.Request.time).Nodup := by
  have hp : FieldCapacity.ClockNoWrap babyBearModulus timestampBase := by decide
  have inverse : SerializedInverse.Clock babyBearModulus := by decide +kernel
  have clocks := state_clock_inputs hp inverse accepted.cpuEquations accepted.states
    initialClock initialAligned
  let callers := trace.rows.filter fun row => row.family == .addSub &&
    decide (Delegation.Requests.Selected row.assignment)
  let rank := fun row : Trace.Row babyBearModulus PooledFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have allUnique := state_clocks_unique hp inverse accepted.cpuEquations accepted.states
    initialClock initialAligned
  have unique : (callers.map rank).Nodup :=
    allUnique.sublist ((show callers.Sublist trace.rows from List.filter_sublist).map rank)
  simp only [pooledCalls, List.map_map, Function.comp_def]
  apply Delegation.Requests.Proofs.shifted_times_unique unique
  intro row member
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  have family : row.family = .addSub := by
    have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using selected
    exact both.1
  have clock := clocks row present
  simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
  have one : Delegation.Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Delegation.Requests.caller, one, rank, Trace.Row.columns, family,
    CircuitLayout.columns, decodeTimestamp, timeOfPair, rawPair] using
    (write_time (by decide)
      (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

/-- The combined request permutation bounds every standard and split worker
clock. No typed decoder registry or separate worker permutation is assumed. -/
theorem unrolled_request_clock_bounds
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    let fulfillments := workers.rows.map Delegation.Requests.fulfillment ++ extraRequests
    (pooledCalls trace).Perm
        (fulfillments.filter fun request => decide (Delegation.Requests.Live request)) ∧
      (∀ request ∈ fulfillments, (timeOfPair request.time).Bounded ∧
        (timeOfPair request.time).lo + 2 < timestampBase) ∧
      ((fulfillments.filter fun request => decide (Delegation.Requests.Live request)).map
        Delegation.Requests.Request.time).Nodup := by
  have clocks := state_clock_inputs (by decide) (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  apply Delegation.Requests.Proofs.bounded_pool accepted.requests
    (fun request member => ?_) (unrolled_request_times_unique accepted initialClock initialAligned)
  unfold pooledCalls at member
  obtain ⟨row, included, rfl⟩ := List.mem_map.mp member
  obtain ⟨present, selected⟩ := List.mem_filter.mp included
  have family : row.family = .addSub := by
    have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using selected
    exact both.1
  have clock := clocks row present
  simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
  exact Delegation.Caller.Proofs.caller_clock (by decide) clock.1 clock.2

end Airbender.Compiler.MachineTargets.Proofs
