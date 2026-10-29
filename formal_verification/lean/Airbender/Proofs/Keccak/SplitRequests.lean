import Airbender.Review.Trace.Workers.Keccak.SplitRequests
import Airbender.Proofs.Delegation.RequestTrace

namespace Airbender.Keccak.Split.Native.Proofs
open Airbender.Trace Airbender.Delegation Airbender.Arithmetic
set_option warningAsError true

theorem caller_member [Fact p.Prime] {data : RequestTrace p}
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    row ∈ data.machine.rows ∧ row.family = .addSub := by
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  have family : row.family = .addSub := by
    cases equal : row.family <;> simp_all [RequestTrace.callers]
  exact ⟨present, family⟩

/-- Native state clocks are unique, so the issued split CSR timestamps are
unique even when the physical worker rows are presented out of order. -/
theorem caller_clocks_unique [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses) :
    (data.calls.map Requests.Request.time).Nodup := by
  have clocks := Airbender.Trace.Proofs.state_clock_inputs hp inverse
    accepted.machineConstraints accepted.states inputs.initialClock inputs.initialAligned
  let rank := fun row : Airbender.Trace.Row p PooledFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have allUnique := Airbender.Trace.Proofs.state_clocks_unique hp inverse
    accepted.machineConstraints accepted.states inputs.initialClock inputs.initialAligned
  have callerUnique : (data.callers.map rank).Nodup :=
    allUnique.sublist ((show data.callers.Sublist data.machine.rows from List.filter_sublist).map rank)
  simp only [RequestTrace.calls, List.map_map, Function.comp_def]
  apply Requests.Proofs.shifted_times_unique callerUnique
  intro row member
  obtain ⟨present, family⟩ := caller_member member
  have clock := clocks row present
  simp only [Airbender.Trace.Row.columns, family, CircuitLayout.columns] at clock
  have one : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Requests.caller, one, rank, Airbender.Trace.Row.columns, family,
    CircuitLayout.columns, decodeTimestamp, timeOfPair, rawPair] using
    (Airbender.Trace.Proofs.write_time (by omega)
      (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

/-- The exact virtual-token permutation matches every nonzero split caller to
a worker of the same full-width CSR and invocation clock. Worker clock bounds
and no low-limb rollover follow from the public initial clock. -/
theorem request_clock_binding [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} (accepted : RequestChecks data)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data before addresses) :
    RequestClockBinding data := by
  have machineClocks := Airbender.Trace.Proofs.state_clock_inputs hp inverse
    accepted.machineConstraints accepted.states inputs.initialClock inputs.initialAligned
  have clocks : ∀ row ∈ data.callers,
      (timeOfPair (Requests.caller row.assignment).time).Bounded ∧
      Requests.Live (Requests.caller row.assignment) ∧
      (timeOfPair (Requests.caller row.assignment).time).lo + 2 < timestampBase := by
    intro row member
    obtain ⟨present, family⟩ := caller_member member
    have facts := machineClocks row present
    simp only [Airbender.Trace.Row.columns, family, CircuitLayout.columns] at facts
    exact Delegation.Caller.Proofs.caller_clock (by omega) facts.1 facts.2
  have unique := caller_clocks_unique hp inverse accepted inputs
  have pool := Requests.Proofs.bounded_pool accepted.requests
    (by
      intro call present
      obtain ⟨row, member, rfl⟩ := List.mem_map.mp present
      exact clocks row member) unique
  refine ⟨pool.1, ?_, ?_, ⟨unique, pool.2.2⟩⟩
  · intro worker present
    exact (pool.2.1 _ (List.mem_map.mpr ⟨worker, present, rfl⟩)).1
  · intro worker present
    exact (pool.2.1 _ (List.mem_map.mpr ⟨worker, present, rfl⟩)).2

/-- Each issued split caller has exactly one physical worker row at its
full-width CSR and invocation clock. -/
theorem unique_issued_worker [Fact p.Prime]
    {data : RequestTrace p} (binding : RequestClockBinding data)
    {row : Airbender.Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    ∃! worker, worker ∈ data.workers.rows ∧
      worker.fulfillment data.workers.cached = Requests.caller row.assignment := by
  let call := Requests.caller row.assignment
  have called : call ∈ data.calls := List.mem_map.mpr ⟨row, member, rfl⟩
  have admitted := binding.fulfilled.mem_iff.mp called
  have live : Requests.Live call := of_decide_eq_true (List.mem_filter.mp admitted).2
  obtain ⟨worker, present, same⟩ := List.mem_map.mp (List.mem_filter.mp admitted).1
  let issued := data.workers.rows.filter fun worker =>
    decide (Requests.Live (worker.fulfillment data.workers.cached))
  have issuedUnique :
      (issued.map fun worker => (worker.fulfillment data.workers.cached).time).Nodup := by
    simpa only [List.filter_map, List.map_map, Function.comp_def, issued,
      RequestTrace.fulfillments]
      using (binding.fulfilled.map Requests.Request.time).nodup_iff.mp
        binding.invocations.1
  have chosen : worker ∈ issued := List.mem_filter.mpr
    ⟨present, by rw [same]; exact decide_eq_true live⟩
  refine ⟨worker, ⟨present, same⟩, ?_⟩
  intro other otherMatch
  have included : other ∈ issued := List.mem_filter.mpr
    ⟨otherMatch.1, by rw [otherMatch.2]; exact decide_eq_true live⟩
  exact List.inj_on_of_nodup_map issuedUnique included chosen
    ((congrArg Requests.Request.time otherMatch.2).trans
      (congrArg Requests.Request.time same).symm)

end Airbender.Keccak.Split.Native.Proofs
