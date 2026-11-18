module
public import Human.Helpers.Delegation.RVSchedule
public import Proven.Delegation.RVRequestTrace
public import Proven.Delegation.RequestWindows

@[expose] public section

/-! RV siblings of the schedule and request-window proofs (`Schedule.lean`, `RequestWindows.lean`) over
    `RVRequestTrace`: state-free conclusions from RV public inputs. The window argument is the generic
    `request_window`. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem rv_issued_worker_slot [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    (binding : RVRequestBinding data before)
    {caller : Trace.Row p PooledFamily} (member : caller ∈ data.callers)
    {worker : Delegation.Row p} (present : worker ∈ data.workers.rows)
    (same : Requests.fulfillment worker = Requests.caller caller.assignment) : WorkerSlot caller worker := by
  obtain ⟨included, family⟩ := rv_caller_member member
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have clock := clocks caller included
  have one : Requests.callerPort.clock.offset = 1 := by rfl
  have issued : (timeOfPair (Requests.caller caller.assignment).time).value = startClock caller + 1 := by
    simpa only [Requests.caller, one, Trace.Row.columns, family, CircuitLayout.columns,
      decodeTimestamp, rawPair, timeOfPair, startClock, Row.clock] using
      (Trace.Proofs.write_time (by omega)
        (base := rawPair caller.assignment caller.columns.initialTime) clock.1 clock.2 (show 1 < 4 by decide)).2
  exact worker_slot_of_clock (by omega) issued
    (Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom caller
      (accepted.constraints caller included) clock.1)
    (binding.clocks worker present) (binding.clockRoom worker present) same

theorem rv_worker_schedule [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    (binding : RVRequestBinding data before) : RVWorkerSchedule data := by
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
    simpa only [RVRequestTrace.calls, List.map_map, Function.comp_def] using binding.invocations.1
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro caller member
    obtain ⟨worker, matched, unique⟩ := rv_unique_issued_worker binding member
    refine ⟨worker, ⟨matched.1, matched.2,
      rv_issued_worker_slot hp inverse accepted inputs binding member matched.1 matched.2⟩, ?_⟩
    intro other checked
    exact unique other ⟨checked.1, checked.2.1⟩
  · intro worker present live
    obtain ⟨caller, member, same⟩ := matchLive worker present live
    refine ⟨caller, ⟨member, same, rv_issued_worker_slot hp inverse accepted inputs binding member present same⟩, ?_⟩
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
    have callerClock := clocks caller (rv_caller_member member).1
    have rowClock := clocks row present
    have finish : finishClock caller = startClock caller + 4 :=
      Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom caller
        (accepted.constraints caller (rv_caller_member member).1) callerClock.1
    have alignedCaller : startClock caller % 4 = 0 := by
      simpa [startClock, Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using callerClock.2
    have alignedRow : startClock row % 4 = 0 := by
      simpa [startClock, Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using rowClock.2
    rw [finish] at overlapping
    omega

theorem rv_request_windows [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    RequestWindowBinding data.callers data.workers lower upper := by
  have binding := rv_request_binding_checks hp clockInverse pcInverse accepted inputs
  have clocks := Trace.Proofs.state_clock_inputs hp clockInverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  apply request_window (by omega)
    (⟨binding.fulfilled, fun worker member => ⟨binding.clocks worker member, binding.clockRoom worker member⟩,
      ?_, ?_, ?_, binding.invocations.1⟩ : WindowFacts data.callers data.workers) first last pastZero
  · intro caller member
    obtain ⟨worker, present, same, _⟩ := binding.workers caller member
    have slot := rv_issued_worker_slot hp clockInverse accepted inputs binding member present same
    exact (congrArg (fun request : Requests.Request p => (timeOfPair request.time).value) same).symm.trans slot.invocation
  · intro caller member
    exact Trace.Proofs.ClockLaws.advance hp clockInverse data.machine.rom caller
      (accepted.constraints caller (rv_caller_member member).1) (clocks caller (rv_caller_member member).1).1
  · intro caller member
    simpa [startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
      using (clocks caller (rv_caller_member member).1).2

end Airbender.Delegation.Caller.Proofs
