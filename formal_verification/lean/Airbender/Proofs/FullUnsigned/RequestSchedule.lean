import Airbender.Proofs.FullUnsigned.MemoryClocks
import Airbender.Proofs.Delegation.NativeInvocation

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Native activity excludes every zero-clock fulfillment in the combined
request pool. Exact matching therefore accounts for every worker row. -/
theorem unrolled_full_requests_match
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    (pooledCalls trace).Perm (workers.rows.map Delegation.Requests.fulfillment ++
      splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)) := by
  have matching := (unrolled_request_clock_bounds accepted initialClock initialAligned).1
  have all : (workers.rows.map Delegation.Requests.fulfillment ++
      splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)).filter
      (fun request => decide (Delegation.Requests.Live request)) =
        workers.rows.map Delegation.Requests.fulfillment ++
          splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) := by
    apply List.filter_eq_self.mpr
    intro request member
    rcases List.mem_append.mp member with standard | split
    · obtain ⟨worker, present, rfl⟩ := List.mem_map.mp standard
      exact decide_eq_true (Delegation.Proofs.active_invocation_live
        (accepted.workerEquations worker present) (accepted.workerActive worker present))
    · obtain ⟨worker, present, rfl⟩ := List.mem_map.mp split
      exact decide_eq_true (Keccak.Split.Native.Proofs.active_invocation_live splitWorkers.cached
        (equations.rowsHold worker present) (active worker present))
  exact all ▸ matching

/-- No two active fulfillments share a raw invocation time, including across
the standard and split worker pools. -/
theorem unrolled_full_fulfillment_times_unique
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    ((workers.rows.map Delegation.Requests.fulfillment ++
      splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)).map
        Delegation.Requests.Request.time).Nodup := by
  have matched := unrolled_full_requests_match accepted equations active initialClock initialAligned
  exact (matched.map Delegation.Requests.Request.time).nodup_iff.mp
    (unrolled_request_times_unique accepted initialClock initialAligned)

/-- Each combined fulfillment has an actual selected CPU caller. Its raw
invocation occurs one slot after that caller's aligned initial clock. -/
theorem unrolled_full_fulfillment_slot
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (request : Delegation.Requests.Request babyBearModulus)
    (member : request ∈ workers.rows.map Delegation.Requests.fulfillment ++
      splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)) :
    ∃ caller ∈ trace.rows, caller.family = .addSub ∧
      Delegation.Requests.Selected caller.assignment ∧
      request = Delegation.Requests.caller caller.assignment ∧
      (decodeTimestamp caller.assignment caller.columns.initialTime).lo % 4 = 0 ∧
      (timeOfPair request.time).value =
        (decodeTimestamp caller.assignment caller.columns.initialTime).value + 1 := by
  have matched := unrolled_full_requests_match accepted equations active initialClock initialAligned
  have called := matched.mem_iff.mpr member
  unfold pooledCalls at called
  obtain ⟨caller, included, equal⟩ := List.mem_map.mp called
  obtain ⟨present, selected⟩ := List.mem_filter.mp included
  have both : caller.family = .addSub ∧ Delegation.Requests.Selected caller.assignment := by
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using selected
  have clock := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned caller present
  refine ⟨caller, present, both.1, both.2, equal.symm, clock.2, ?_⟩
  rw [← equal]
  simp only [Trace.Row.columns, both.1, CircuitLayout.columns] at clock ⊢
  have one : Delegation.Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Delegation.Requests.caller, one, decodeTimestamp, timeOfPair, rawPair] using
    (write_time (by decide)
      (base := rawPair caller.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

/-- Every standard worker's physical events occupy its own caller's final
cycle slot. The caller comes from the complete combined request ledger. -/
theorem unrolled_full_standard_worker_slot
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (worker : Delegation.Row babyBearModulus) (present : worker ∈ workers.rows) :
    ∃ caller ∈ trace.rows, caller.family = .addSub ∧
      Delegation.Requests.Selected caller.assignment ∧
      Delegation.Requests.fulfillment worker = Delegation.Requests.caller caller.assignment ∧
      ∀ port ∈ worker.ports,
        (transferEvent (readToken worker.assignment port, worker.writeToken port)).1 =
          (decodeTimestamp caller.assignment caller.columns.initialTime).value + 4 := by
  have member : Delegation.Requests.fulfillment worker ∈
      workers.rows.map Delegation.Requests.fulfillment ++
        splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) :=
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨worker, present, rfl⟩))
  obtain ⟨caller, included, family, selected, equal, _, time⟩ :=
    unrolled_full_fulfillment_slot accepted equations active initialClock initialAligned _ member
  have clock := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1 _ member
  refine ⟨caller, included, family, selected, equal, ?_⟩
  intro port physical
  have offset := Delegation.Proofs.port_offset worker physical
  have written := (write_time_of_room (by decide) (offset := port.clock.offset)
    (base := rawPair worker.assignment worker.columns.invocation) clock.1
    (by simpa only [offset, Delegation.Requests.fulfillment, timeOfPair, rawPair] using clock.2)).2
  have value : (timeOfPair (worker.writeToken port).time).value =
      (timeOfPair (Delegation.Requests.fulfillment worker).time).value + 2 := by
    simpa only [Delegation.Row.writeToken, offset, Delegation.Requests.fulfillment] using written
  change (timeOfPair (worker.writeToken port).time).value + 1 = _
  omega

/-- Every split worker's physical events occupy its own caller's final
cycle slot in either imported cache mode. -/
theorem unrolled_full_split_worker_slot
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (equations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (worker : Keccak.Split.Native.Row babyBearModulus) (present : worker ∈ splitWorkers.rows) :
    ∃ caller ∈ trace.rows, caller.family = .addSub ∧
      Delegation.Requests.Selected caller.assignment ∧
      worker.fulfillment splitWorkers.cached = Delegation.Requests.caller caller.assignment ∧
      ∀ port ∈ worker.ports splitWorkers.cached,
        (transferEvent (readToken worker.assignment port, worker.writeToken splitWorkers.cached port)).1 =
          (decodeTimestamp caller.assignment caller.columns.initialTime).value + 4 := by
  have member : worker.fulfillment splitWorkers.cached ∈
      workers.rows.map Delegation.Requests.fulfillment ++
        splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached) :=
    List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨worker, present, rfl⟩))
  obtain ⟨caller, included, family, selected, equal, _, time⟩ :=
    unrolled_full_fulfillment_slot accepted equations active initialClock initialAligned _ member
  have clock := (unrolled_request_clock_bounds accepted initialClock initialAligned).2.1 _ member
  refine ⟨caller, included, family, selected, equal, ?_⟩
  intro port physical
  have offset := Keccak.Split.Native.Proofs.port_offset splitWorkers.cached worker physical
  have written := (write_time_of_room (by decide) (offset := port.clock.offset)
    (base := rawPair worker.assignment (worker.columns splitWorkers.cached).invocation) clock.1
    (by simpa only [offset, Keccak.Split.Native.Row.fulfillment, timeOfPair, rawPair] using clock.2)).2
  have value : (timeOfPair (worker.writeToken splitWorkers.cached port).time).value =
      (timeOfPair (worker.fulfillment splitWorkers.cached).time).value + 2 := by
    simpa only [Keccak.Split.Native.Row.writeToken, offset, Keccak.Split.Native.Row.fulfillment] using written
  change (timeOfPair (worker.writeToken splitWorkers.cached port).time).value + 1 = _
  omega

end Airbender.Compiler.MachineTargets.Proofs
