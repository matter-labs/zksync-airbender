import Airbender.Review.Delegation.Schedule
import Airbender.Proofs.Delegation.RequestTrace

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem issued_worker_slot [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (binding : RequestBinding data before)
    {caller : Trace.Row p PooledFamily} (member : caller ∈ data.callers)
    {worker : Delegation.Row p} (present : worker ∈ data.workers.rows)
    (same : Requests.fulfillment worker = Requests.caller caller.assignment) : WorkerSlot caller worker := by
  obtain ⟨included, family⟩ := caller_member member
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have clock := clocks caller included
  have one : Requests.callerPort.clock.offset = 1 := rfl
  have invocation : (decodeTimestamp worker.assignment worker.columns.invocation).value = startClock caller + 1 := by
    have time := congrArg (fun request : Requests.Request p => (timeOfPair request.time).value) same
    have issued := (Trace.Proofs.write_time (by omega)
      (base := rawPair caller.assignment caller.columns.initialTime) clock.1 clock.2 (show 1 < 4 by decide)).2
    have issued : (timeOfPair (Requests.caller caller.assignment).time).value = startClock caller + 1 := by
      simpa only [Requests.caller, one, Trace.Row.columns, family, CircuitLayout.columns,
        decodeTimestamp, rawPair, timeOfPair, startClock] using issued
    exact time.trans issued
  refine ⟨invocation, ?_, ?_⟩
  · intro port portMember
    have offset := Delegation.Proofs.port_offset worker portMember
    have written := (Trace.Proofs.write_time_of_room (by omega)
      (base := rawPair worker.assignment worker.columns.invocation) (offset := port.clock.offset)
      (binding.clocks worker present)
      (by simpa only [offset, decodeTimestamp, rawPair] using binding.clockRoom worker present)).2
    change (timeOfPair (worker.writeToken port).time).value =
      (decodeTimestamp worker.assignment worker.columns.invocation).value + port.clock.offset at written
    rw [written, offset, invocation]
  · exact Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom caller
      (accepted.constraints caller included) clock.1

theorem worker_schedule [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (binding : RequestBinding data before) : WorkerSchedule data := by
  have matchLive : ∀ worker ∈ data.workers.rows, Requests.Live (Requests.fulfillment worker) →
      ∃ caller ∈ data.callers, Requests.fulfillment worker = Requests.caller caller.assignment := by
    intro worker present live
    have fulfilled : Requests.fulfillment worker ∈ data.fulfillments.filter
        (fun request => decide (Requests.Live request)) :=
      List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, present, rfl⟩, decide_eq_true live⟩
    obtain ⟨caller, member, same⟩ := List.mem_map.mp (binding.fulfilled.mem_iff.mpr fulfilled)
    exact ⟨caller, member, same.symm⟩
  have calledLive : ∀ caller ∈ data.callers, Requests.Live (Requests.caller caller.assignment) := by
    intro caller member
    exact of_decide_eq_true (List.mem_filter.mp (binding.fulfilled.mem_iff.mp
      (List.mem_map.mpr ⟨caller, member, rfl⟩))).2
  have callerUnique : (data.callers.map (fun caller => (Requests.caller caller.assignment).time)).Nodup := by
    simpa only [RequestTrace.calls, List.map_map, Function.comp_def] using binding.invocations.1
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro caller member
    obtain ⟨worker, matched, unique⟩ := unique_issued_worker binding member
    refine ⟨worker, ⟨matched.1, matched.2,
      issued_worker_slot hp inverse accepted inputs binding member matched.1 matched.2⟩, ?_⟩
    intro other checked
    exact unique other ⟨checked.1, checked.2.1⟩
  · intro worker present live
    obtain ⟨caller, member, same⟩ := matchLive worker present live
    refine ⟨caller, ⟨member, same, issued_worker_slot hp inverse accepted inputs binding member present same⟩, ?_⟩
    intro other checked
    exact List.inj_on_of_nodup_map callerUnique checked.1 member
      (congrArg Requests.Request.time (checked.2.1.symm.trans same))
  · intro worker present
    constructor
    · intro missing
      by_contra live
      exact missing (matchLive worker present live)
    · intro zero ⟨caller, member, same⟩
      exact calledLive caller member ((congrArg Requests.Request.time same).symm.trans zero)
  · intro caller member row present overlapping
    have callerClock := clocks caller (caller_member member).1
    have rowClock := clocks row present
    have finish : finishClock caller = startClock caller + 4 :=
      Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom caller
        (accepted.constraints caller (caller_member member).1) callerClock.1
    have alignedCaller : startClock caller % 4 = 0 := by
      simpa [startClock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using callerClock.2
    have alignedRow : startClock row % 4 = 0 := by
      simpa [startClock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using rowClock.2
    rw [finish] at overlapping
    omega

end Airbender.Delegation.Caller.Proofs
