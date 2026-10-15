import Airbender.Review.Helpers.Delegation.RequestWindows
import Airbender.Review.Helpers.Delegation.SpanABI
import Airbender.Proofs.Delegation.Schedule

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
variable {Kind : Type} [CircuitLayout Kind]
set_option warningAsError true

structure WindowFacts [Fact p.Prime] (callers : List (Trace.Row p Kind)) (workers : MemoryData p) : Prop where
  fulfilled : (callers.map fun caller => Requests.caller caller.assignment).Perm
    ((workers.rows.map Requests.fulfillment).filter fun request => decide (Requests.Live request))
  clocks : ∀ worker ∈ workers.rows,
    (decodeTimestamp worker.assignment worker.columns.invocation).Bounded ∧
    (decodeTimestamp worker.assignment worker.columns.invocation).lo + 2 < timestampBase
  issued : ∀ caller ∈ callers,
    (timeOfPair (Requests.caller caller.assignment).time).value = startClock caller + 1
  advance : ∀ caller ∈ callers, finishClock caller = startClock caller + 4
  aligned : ∀ caller ∈ callers, startClock caller % 4 = 0
  unique : ((callers.map fun caller => Requests.caller caller.assignment).map Requests.Request.time).Nodup

theorem worker_write_time [Fact p.Prime] (hp : timestampBase < p) {worker : Delegation.Row p}
    (bound : (decodeTimestamp worker.assignment worker.columns.invocation).Bounded)
    (room : (decodeTimestamp worker.assignment worker.columns.invocation).lo + 2 < timestampBase) :
    worker.writeTime = (timeOfPair (Requests.fulfillment worker).time).value + 2 := by
  exact (Trace.Proofs.write_time_of_room hp (base := rawPair worker.assignment worker.columns.invocation)
    (offset := 2) bound room).2

theorem caller_window_clock {caller : Trace.Row p Kind} {lower upper : Nat}
    (aligned : startClock caller % 4 = 0) (first : lower % 4 = 0) (last : upper % 4 = 0) :
    (lower < startClock caller + 3 ∧ startClock caller + 3 ≤ upper) ↔
      (lower ≤ startClock caller ∧ startClock caller < upper) := by omega

theorem request_window [Fact p.Prime] (hp : timestampBase < p)
    {callers : List (Trace.Row p Kind)} {workers : MemoryData p}
    (facts : WindowFacts callers workers) {lower upper : Nat}
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    RequestWindowBinding callers workers lower upper := by
  let selected := fun request : Requests.Request p =>
    decide (lower < (timeOfPair request.time).value + 2 ∧ (timeOfPair request.time).value + 2 ≤ upper)
  have workerClock := fun worker member => worker_write_time hp
    (facts.clocks worker member).1 (facts.clocks worker member).2
  have callerFilter : (callers.map fun caller => Requests.caller caller.assignment).filter selected =
      (windowCallers callers lower upper).map fun caller => Requests.caller caller.assignment := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro caller member
    simp only [Function.comp_def, selected, facts.issued caller member]
    simp only [caller_window_clock (facts.aligned caller member) first last]
  have workerFilter : ((workers.rows.map Requests.fulfillment).filter
      (fun request => decide (Requests.Live request))).filter selected =
      (workers.windowRows lower upper).map Requests.fulfillment := by
    rw [List.filter_filter, List.filter_map]
    congr 1
    apply List.filter_congr
    intro worker member
    have time := workerClock worker member
    by_cases live : Requests.Live (Requests.fulfillment worker)
    · simp only [Function.comp_def, selected, time,
        decide_eq_true live, Bool.and_true]
    · have zero : (Requests.fulfillment worker).time = (0, 0) := by simpa [Requests.Live] using live
      have write : worker.writeTime = 2 := by simp [time, zero, timeOfPair, Timestamp.value]
      simp only [Function.comp_def, selected, decide_eq_false live, Bool.and_false]
      simp [write, Nat.not_lt.mpr pastZero]
  have fulfilled := facts.fulfilled.filter selected
  rw [callerFilter, workerFilter] at fulfilled
  have slot : ∀ caller ∈ callers, ∀ worker ∈ workers.rows,
      Requests.fulfillment worker = Requests.caller caller.assignment → WorkerSlot caller worker := by
    intro caller member worker present same
    exact worker_slot_of_clock hp (facts.issued caller member) (facts.advance caller member)
      (facts.clocks worker present).1 (facts.clocks worker present).2 same
  have inWindow : ∀ caller ∈ callers, ∀ worker ∈ workers.rows,
      Requests.fulfillment worker = Requests.caller caller.assignment →
      (worker ∈ workers.windowRows lower upper ↔ caller ∈ windowCallers callers lower upper) := by
    intro caller member worker present same
    have time : worker.writeTime = startClock caller + 3 := by
      rw [workerClock worker present, same, facts.issued caller member]
    simp only [MemoryData.windowRows, windowCallers, List.mem_filter, decide_eq_true_eq]
    rw [time, caller_window_clock (facts.aligned caller member) first last]
    simp only [present, member, true_and]
  have unique : (callers.map fun caller => (Requests.caller caller.assignment).time).Nodup := by
    simpa only [List.map_map, Function.comp_def] using facts.unique
  refine ⟨fulfilled, ?_, ?_, ?_⟩
  · intro caller member
    have included := List.mem_of_mem_filter member
    obtain ⟨worker, matched, only⟩ := Requests.Proofs.unique_fulfillment facts.fulfilled facts.unique
      (List.mem_map.mpr ⟨caller, included, rfl⟩)
    refine ⟨worker, ⟨(inWindow caller included worker matched.1 matched.2).mpr member,
      matched.2, slot caller included worker matched.1 matched.2⟩, ?_⟩
    intro other checked
    exact only other ⟨List.mem_of_mem_filter checked.1, checked.2.1⟩
  · intro worker present
    obtain ⟨caller, member, same⟩ := List.mem_map.mp (fulfilled.mem_iff.mpr
      (List.mem_map.mpr ⟨worker, present, rfl⟩))
    refine ⟨caller, ⟨member, same.symm,
      slot caller (List.mem_of_mem_filter member) worker (List.mem_of_mem_filter present) same.symm⟩, ?_⟩
    intro other checked
    exact List.inj_on_of_nodup_map unique (List.mem_of_mem_filter checked.1)
      (List.mem_of_mem_filter member) (congrArg Requests.Request.time (checked.2.1.symm.trans same.symm))
  · intro worker present zero
    have write : worker.writeTime = 2 := by
      simp [workerClock worker present, zero, timeOfPair, Timestamp.value]
    simp [MemoryData.prefixRows, MemoryData.windowRows, present, write, pastZero, Nat.not_lt.mpr pastZero]

theorem window_call_count [Fact p.Prime] {callers : List (Trace.Row p Kind)} {workers : MemoryData p}
    {lower upper : Nat} (binding : RequestWindowBinding callers workers lower upper) :
    (windowCallers callers lower upper).length = (workers.windowRows lower upper).length := by
  simpa only [List.length_map] using binding.fulfilled.length_eq

theorem window_hash_calls [Fact p.Prime] {callers : List (Trace.Row p Kind)} {workers : MemoryData p}
    {lower upper : Nat} (binding : RequestWindowBinding callers workers lower upper) {span : HashSpan}
    (family : ∀ worker ∈ workers.windowRows lower upper, worker.family = span.family)
    (count : (workers.windowRows lower upper).length = span.callCount) :
    (windowCallers callers lower upper).length = span.callCount ∧
    ∀ caller ∈ windowCallers callers lower upper,
      (Requests.caller caller.assignment).csr = Requests.csr span.family := by
  refine ⟨(window_call_count binding).trans count, ?_⟩
  intro caller member
  obtain ⟨worker, matched, _⟩ := binding.callerMatches caller member
  exact (congrArg Requests.Request.csr matched.2.1).symm.trans
    (congrArg Requests.csr (family worker matched.1))

theorem request_windows [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    RequestWindowBinding data.callers data.workers lower upper := by
  have binding := request_binding_checks hp clockInverse pcInverse accepted inputs
  have clocks := Trace.Proofs.state_clock_inputs hp clockInverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  apply request_window (by omega)
    (⟨binding.fulfilled, fun worker member => ⟨binding.clocks worker member, binding.clockRoom worker member⟩,
      ?_, ?_, ?_, binding.invocations.1⟩ : WindowFacts data.callers data.workers) first last pastZero
  · intro caller member
    obtain ⟨worker, present, same, _⟩ := binding.workers caller member
    have slot := issued_worker_slot hp clockInverse accepted inputs binding member present same
    exact (congrArg (fun request : Requests.Request p => (timeOfPair request.time).value) same).symm.trans slot.invocation
  · intro caller member
    exact Trace.Proofs.ClockLaws.advance hp clockInverse data.machine.rom caller
      (accepted.constraints caller (caller_member member).1) (clocks caller (caller_member member).1).1
  · intro caller member
    simpa [startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
      using (clocks caller (caller_member member).1).2

end Airbender.Delegation.Caller.Proofs
