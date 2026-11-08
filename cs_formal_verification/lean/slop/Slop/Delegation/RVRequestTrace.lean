module
public import Human.Trace.Delegation.RVRequestTrace
public import Slop.Delegation.RVCallerDecoder
public import Slop.Delegation.RequestTrace
public import Slop.Final.Trace.Delegation.RVTheorems

@[expose] public section

/-! RV siblings of the request-binding proofs (`RequestTrace.lean`) over `RVRequestTrace`. The clock and matching
    arguments are the Sail-free ones (`caller_clock`, `csr_injective`, `Requests.Proofs.*`); the caller rows use
    `rv_caller_binding`/`rv_pc_binding`. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem rv_caller_member [Fact p.Prime] {data : RVRequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    row ∈ data.machine.rows ∧ row.family = .addSub := by
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  have family : row.family = .addSub := by
    cases equal : row.family <;> simp_all
  exact ⟨present, family⟩

theorem rv_caller_clocks_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} (accepted : RVRequestChecks data)
    (inputs : RVRequestInputs data before addresses) : (data.calls.map Requests.Request.time).Nodup := by
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  let rank := fun row : Trace.Row p PooledFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have allUnique := Trace.Proofs.state_clocks_unique hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have callerUnique : (data.callers.map rank).Nodup :=
    allUnique.sublist ((show data.callers.Sublist data.machine.rows from List.filter_sublist).map rank)
  simp only [RVRequestTrace.calls, List.map_map, Function.comp_def]
  apply Requests.Proofs.shifted_times_unique callerUnique
  intro row member
  obtain ⟨present, family⟩ := rv_caller_member member
  have clock := clocks row present
  simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
  have one : Requests.callerPort.clock.offset = 1 := by rfl
  simpa only [Requests.caller, one, rank, Trace.Row.columns, family, CircuitLayout.columns,
    decodeTimestamp, timeOfPair, rawPair] using
    (Trace.Proofs.write_time (by omega) (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

theorem rv_request_binding_checks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} (accepted : RVRequestChecks data)
    (inputs : RVRequestInputs data before addresses) : RVRequestBinding data before := by
  have machineClocks := Trace.Proofs.state_clock_inputs hp clockInverse
    accepted.constraints accepted.states inputs.initialClock inputs.initialAligned
  have clocks : ∀ row ∈ data.callers,
      (timeOfPair (Requests.caller row.assignment).time).Bounded ∧
      Requests.Live (Requests.caller row.assignment) ∧
      (timeOfPair (Requests.caller row.assignment).time).lo + 2 < timestampBase := by
    intro row member
    obtain ⟨present, family⟩ := rv_caller_member member
    have facts := machineClocks row present
    simp only [Trace.Row.columns, family, CircuitLayout.columns] at facts
    exact caller_clock (by omega) facts.1 facts.2
  have unique := rv_caller_clocks_unique hp clockInverse accepted inputs
  have pool := Requests.Proofs.bounded_pool accepted.requests
    (by
      intro call present
      obtain ⟨row, member, rfl⟩ := List.mem_map.mp present
      exact clocks row member) unique
  have fulfilled := pool.1
  have bindings : ∀ row ∈ data.callers,
      RVBinding row.assignment before data.program ∧ RVPCBinding row.assignment before data.program := by
    intro row member
    obtain ⟨present, family⟩ := rv_caller_member member
    have core := accepted.constraints row present
    simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
    have constraints := Verification.holds_of_sublist core
      (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
    exact ⟨rv_caller_binding (by norm_num [timestampBase] at hp; omega) constraints inputs.image
        (accepted.decoded row member),
      rv_pc_binding (by norm_num [timestampBase] at hp; omega) pcInverse constraints inputs.image
        (accepted.decoded row member)⟩
  have workerClocks : ∀ row ∈ data.workers.rows,
      (timeOfPair (Requests.fulfillment row).time).Bounded ∧
      (timeOfPair (Requests.fulfillment row).time).lo + 2 < timestampBase := by
    intro worker present
    exact pool.2.1 _ (List.mem_map.mpr ⟨worker, present, rfl⟩)
  refine ⟨bindings, fulfilled, ?_, ?_, ?_, ?_⟩
  · intro row member
    have callMember : Requests.caller row.assignment ∈ data.calls := List.mem_map.mpr ⟨row, member, rfl⟩
    have matchMember := (List.mem_filter.mp (fulfilled.mem_iff.mp callMember)).1
    obtain ⟨worker, workerMember, same⟩ := List.mem_map.mp matchMember
    obtain ⟨entry, present, source, _, _, address⟩ := (bindings row member).1.instruction
    refine ⟨worker, workerMember, same, entry, present, source, ?_⟩
    apply csr_injective
    exact (congrArg Requests.Request.csr same).trans address
  · intro row member
    simpa only [Requests.fulfillment, timeOfPair, rawPair, decodeTimestamp] using (workerClocks row member).1
  · intro row member
    simpa only [Requests.fulfillment, timeOfPair, rawPair, decodeTimestamp] using (workerClocks row member).2
  · exact ⟨unique, pool.2.2⟩

theorem rv_request_binding [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} (accepted : RVRequestAccepted data)
    (inputs : RVRequestInputs data before addresses) : RVRequestBinding data before :=
  rv_request_binding_checks hp clockInverse pcInverse accepted.toRVRequestChecks inputs

theorem rv_unique_issued_worker [Fact p.Prime]
    {data : RVRequestTrace p} {before : RV.State}
    (binding : RVRequestBinding data before) {row : Trace.Row p PooledFamily}
    (member : row ∈ data.callers) :
    ∃! worker, worker ∈ data.workers.rows ∧ Requests.fulfillment worker = Requests.caller row.assignment :=
  Requests.Proofs.unique_fulfillment binding.fulfilled binding.invocations.1
    (List.mem_map.mpr ⟨row, member, rfl⟩)

/-- The worker pool's RV seed inputs, with the clock room proved by request binding. -/
theorem rv_request_worker_inputs [Fact p.Prime] {data : RVRequestTrace p} {before : RV.State}
    {cells : List Cell} (requests : RVRequestBinding data before)
    (initialization : initialImageRV before cells = some data.workers.initial)
    (distinct : (cells.map Cell.addressCode).Nodup) : RVMemoryInputs data.workers before cells :=
  ⟨initialization, distinct, requests.clockRoom, fun row member => (requests.clocks row member).2⟩

theorem rv_request_memory_execution [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RVRequestAccepted data) (inputs : RVRequestMemoryInputs data before addresses cells) :
    RVRequestExecution data before cells := by
  have requests := rv_request_binding hp clockInverse pcInverse accepted inputs.publicProgram
  have publicState := rv_request_worker_inputs requests inputs.initialization inputs.distinct
  exact ⟨requests, Delegation.rv_memory_soundness hp accepted.workers publicState,
    Delegation.rv_native_memory_execution hp accepted.workers publicState inputs.aligned⟩

end Airbender.Delegation.Caller.Proofs
