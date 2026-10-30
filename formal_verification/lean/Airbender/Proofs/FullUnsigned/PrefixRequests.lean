import Airbender.Proofs.FullUnsigned.PrefixMemory

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

private theorem prefix_calls
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ trace.rows)
    (memory : List (MemoryToken babyBearModulus)) :
    pooledCalls (unrolledFullPrefixTrace trace next.start memory) =
      (pooledCalls trace).filter fun request => decide ((timeOfPair request.time).value + 3 ≤ next.clock) := by
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have aligned (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows) : row.clock % 4 = 0 := by
    simpa [Trace.Row.clock, decodeTimestamp, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
      using (clocks row present).2
  have cut := aligned next member
  simp only [pooledCalls, unrolledFullPrefixTrace, List.filter_filter, List.filter_map]
  congr 1
  apply List.filter_congr
  intro row present
  cases chosen : (row.family == .addSub && decide (Delegation.Requests.Selected row.assignment)) with
  | false => simp only [Bool.false_and, Bool.and_false]
  | true =>
    have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using chosen
    have clock := clocks row present
    have rowAligned := aligned row present
    have time : (timeOfPair (Delegation.Requests.caller row.assignment).time).value = row.clock + 1 := by
      simp only [Trace.Row.columns, both.1, CircuitLayout.columns] at clock
      have one : Delegation.Requests.callerPort.clock.offset = 1 := rfl
      simpa only [Delegation.Requests.caller, one, Trace.Row.clock, Trace.Row.columns,
        both.1, CircuitLayout.columns, decodeTimestamp, timeOfPair, rawPair] using
        (write_time (by decide) (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
          clock.1 clock.2 (show 1 < 4 by decide)).2
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.true_and, Bool.and_true, Function.comp_def, decide_eq_true_eq]
    change row.clock < next.clock ↔ (timeOfPair (Delegation.Requests.caller row.assignment).time).value + 3 ≤ next.clock
    omega

/-- The exact combined request ledger restricts to the same actual native prefix.
Standard and split requests use one cut. No independent prefix match is assumed. -/
theorem unrolled_full_prefix_requests
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {next : Trace.Row babyBearModulus PooledFamily} (member : next ∈ trace.rows)
    (memory : List (MemoryToken babyBearModulus)) :
    Delegation.Requests.Matching (pooledCalls (unrolledFullPrefixTrace trace next.start memory))
      ((unrolledFullPrefixWorkers workers next.start).rows.map Delegation.Requests.fulfillment ++
        (unrolledFullPrefixSplitWorkers splitWorkers next.start).rows.map
          (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)) := by
  let choose := fun request : Delegation.Requests.Request babyBearModulus =>
    decide ((timeOfPair request.time).value + 3 ≤ next.clock)
  have calls := prefix_calls accepted initialClock initialAligned member memory
  have fulfillments :
      (unrolledFullPrefixWorkers workers next.start).rows.map Delegation.Requests.fulfillment ++
        (unrolledFullPrefixSplitWorkers splitWorkers next.start).rows.map
          (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) =
      (workers.rows.map Delegation.Requests.fulfillment ++
        splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)).filter choose := by
    simp only [unrolledFullPrefixWorkers, unrolledFullPrefixSplitWorkers, List.filter_append, List.filter_map]
    rfl
  have filtered := (unrolled_full_requests_match accepted equations active initialClock initialAligned).filter choose
  rw [← calls, ← fulfillments] at filtered
  exact ((filtered.map Delegation.Requests.Request.issued).append
    (filtered.symm.map Delegation.Requests.Request.empty)).trans List.perm_append_comm

end Airbender.Compiler.MachineTargets.Proofs
