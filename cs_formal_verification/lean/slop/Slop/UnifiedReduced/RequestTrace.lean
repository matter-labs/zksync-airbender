import Human.Helpers.UnifiedReduced.RequestTrace
import Slop.UnifiedReduced.Delegation
import Slop.UnifiedReduced.Trace
import Slop.Delegation.Schedule

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem request_binding [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses) : RequestBinding data before := by
  have member : ∀ row ∈ data.callers, row ∈ data.machine.rows :=
    fun _ present => (List.mem_filter.mp present).1
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have issued : ∀ row ∈ data.callers,
      (timeOfPair (request row.assignment).time).value = Delegation.Caller.startClock row + 1 := by
    intro row present
    have clock := clocks row (member row present)
    have one : Delegation.Requests.callerPort.clock.offset = 1 := rfl
    simpa only [request, Delegation.Requests.caller, one, Delegation.Caller.startClock, Trace.Row.clock,
      Trace.Row.columns, CircuitLayout.columns, decodeTimestamp, rawPair, timeOfPair,
      AddSub.importedConstraintsTraceColumns, importedConstraintsTraceColumns] using
      (Trace.Proofs.write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
        clock.1 clock.2 (show 1 < 4 by decide)).2
  have callClocks : ∀ call ∈ data.calls, (timeOfPair call.time).Bounded ∧ Delegation.Requests.Live call ∧
      (timeOfPair call.time).lo + 2 < timestampBase := by
    intro call present
    obtain ⟨row, included, rfl⟩ := List.mem_map.mp present
    have clock := clocks row (member row included)
    exact Delegation.Caller.Proofs.caller_clock (by omega) clock.1 clock.2
  have unique : (data.calls.map Delegation.Requests.Request.time).Nodup := by
    have allUnique := Trace.Proofs.state_clocks_unique hp inverse accepted.constraints accepted.states
      inputs.initialClock inputs.initialAligned
    have callerUnique := allUnique.sublist
      ((show data.callers.Sublist data.machine.rows from List.filter_sublist).map
        (fun row => (decodeTimestamp row.assignment row.columns.initialTime).value))
    simpa only [RequestTrace.calls, List.map_map, Function.comp_def] using
      Delegation.Requests.Proofs.shifted_times_unique callerUnique issued
  have pool := Delegation.Requests.Proofs.bounded_pool accepted.requests callClocks unique
  have workerClocks : ∀ worker ∈ data.workers.rows,
      (decodeTimestamp worker.assignment worker.columns.invocation).Bounded ∧
      (decodeTimestamp worker.assignment worker.columns.invocation).lo + 2 < timestampBase := by
    intro worker present
    exact pool.2.1 _ (List.mem_map.mpr ⟨worker, present, rfl⟩)
  have bindings : ∀ row ∈ data.callers, Binding row.assignment before data.program := by
    intro row present
    have constraints := accepted.constraints row (member row present)
    have core := Verification.holds_of_sublist constraints
      (List.sublist_append_left _ importedConstraintsTimestampLookups)
    exact caller_binding (by norm_num [timestampBase] at hp; omega) core inputs.image (accepted.decoded row present)
  refine ⟨bindings, pool.1, ?_, workerClocks, ⟨unique, pool.2.2⟩, ?_, ?_⟩
  · intro row present
    obtain ⟨worker, matched, only⟩ := Delegation.Requests.Proofs.unique_fulfillment pool.1 unique
      (List.mem_map.mpr ⟨row, present, rfl⟩)
    have clock := clocks row (member row present)
    have advance := Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom row
      (accepted.constraints row (member row present)) clock.1
    refine ⟨worker, ⟨matched.1, matched.2,
      Delegation.Caller.Proofs.worker_slot_of_clock (by omega) (issued row present) advance
        (workerClocks worker matched.1).1 (workerClocks worker matched.1).2 matched.2⟩, ?_⟩
    intro other checked
    exact only other ⟨checked.1, checked.2.1⟩
  · intro worker present
    constructor
    · intro missing
      by_contra nonzero
      have included : Delegation.Requests.fulfillment worker ∈
          data.fulfillments.filter (fun call => decide (Delegation.Requests.Live call)) :=
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, present, rfl⟩, decide_eq_true nonzero⟩
      obtain ⟨row, rowMember, same⟩ := List.mem_map.mp (pool.1.mem_iff.mpr included)
      exact missing ⟨row, rowMember, same.symm⟩
    · intro zero ⟨row, rowMember, same⟩
      exact (callClocks _ (List.mem_map.mpr ⟨row, rowMember, rfl⟩)).2.1
        ((congrArg Delegation.Requests.Request.time same).symm.trans zero)
  · intro caller present row included overlapping
    have callerClock := clocks caller (member caller present)
    have rowClock := clocks row included
    have advance : Delegation.Caller.finishClock caller = Delegation.Caller.startClock caller + 4 :=
      Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom caller
        (accepted.constraints caller (member caller present)) callerClock.1
    have callerAligned : Delegation.Caller.startClock caller % 4 = 0 := by
      simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using callerClock.2
    have rowAligned : Delegation.Caller.startClock row % 4 = 0 := by
      simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using rowClock.2
    rw [advance] at overlapping
    omega

end Airbender.UnifiedReduced.Caller.Proofs
