import Slop.Final.Trace.Delegation.Theorems
import Human.Trace.Delegation.RequestTrace
import Slop.Delegation.CallerPC
import Slop.Trace.Pooled
import Slop.Trace.Slots

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem caller_clock [Fact p.Prime] (hp : timestampBase < p)
    {w : Nat → ZMod p}
    (bound : (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).Bounded)
    (aligned : (decodeTimestamp w AddSub.importedConstraintsTraceColumns.initialTime).lo % 4 = 0) :
    (timeOfPair (Requests.caller w).time).Bounded ∧ Requests.Live (Requests.caller w) ∧
    (timeOfPair (Requests.caller w).time).lo + 2 < timestampBase := by
  let base := rawPair w AddSub.importedConstraintsTraceColumns.initialTime
  have bounds : (timeOfPair base).Bounded := bound
  have alignment : base.1.val % 4 = 0 := aligned
  have room : base.1.val + 1 < timestampBase := by
    have low := bounds.1
    norm_num [timeOfPair, timestampBase] at low ⊢
    omega
  have clock := Trace.Proofs.write_time_of_room hp bounds room
  have canonical : (base.1 + (1 : ZMod p)).val = base.1.val + 1 := by
    calc
      _ = ((base.1.val + 1 : Nat) : ZMod p).val := by simp only [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
      _ = base.1.val + 1 := ZMod.val_natCast_of_lt (lt_trans room hp)
  have token : (Requests.caller w).time = (base.1 + 1, base.2) := by
    change (base.1 + ((1 : Nat) : ZMod p), base.2) = (base.1 + 1, base.2)
    simp only [Nat.cast_one]
  refine ⟨by simpa only [token, Nat.cast_one] using clock.1, ?_, ?_⟩
  · intro equal
    have low := congrArg (fun pair : ZMod p × ZMod p => pair.1.val) equal
    rw [token] at low
    simp only [canonical, ZMod.val_zero] at low
    omega
  · rw [token]
    change (base.1 + 1).val + 2 < timestampBase
    rw [canonical]
    have low := bounds.1
    norm_num [timeOfPair, timestampBase] at low ⊢
    omega

theorem csr_injective : Function.Injective Requests.csr := by
  intro first last equal
  cases first <;> cases last <;> first | rfl | contradiction

theorem caller_member [Fact p.Prime] {data : RequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    row ∈ data.machine.rows ∧ row.family = .addSub := by
  obtain ⟨present, selected⟩ := List.mem_filter.mp member
  have family : row.family = .addSub := by
    cases equal : row.family <;> simp_all
  exact ⟨present, family⟩

theorem caller_clocks_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data)
    (inputs : RequestInputs data before addresses) : (data.calls.map Requests.Request.time).Nodup := by
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  let rank := fun row : Trace.Row p PooledFamily =>
    (decodeTimestamp row.assignment row.columns.initialTime).value
  have allUnique := Trace.Proofs.state_clocks_unique hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have callerUnique : (data.callers.map rank).Nodup :=
    allUnique.sublist ((show data.callers.Sublist data.machine.rows from List.filter_sublist).map rank)
  simp only [RequestTrace.calls, List.map_map, Function.comp_def]
  apply Requests.Proofs.shifted_times_unique callerUnique
  intro row member
  obtain ⟨present, family⟩ := caller_member member
  have clock := clocks row present
  simp only [Trace.Row.columns, family, CircuitLayout.columns] at clock
  have one : Requests.callerPort.clock.offset = 1 := rfl
  simpa only [Requests.caller, one, rank, Trace.Row.columns, family, CircuitLayout.columns,
    decodeTimestamp, timeOfPair, rawPair] using
    (Trace.Proofs.write_time (by omega) (base := rawPair row.assignment AddSub.importedConstraintsTraceColumns.initialTime)
      clock.1 clock.2 (show 1 < 4 by decide)).2

theorem request_binding_checks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestChecks data)
    (inputs : RequestInputs data before addresses) : RequestBinding data before := by
  have machineClocks := Trace.Proofs.state_clock_inputs hp clockInverse
    accepted.constraints accepted.states inputs.initialClock inputs.initialAligned
  have clocks : ∀ row ∈ data.callers,
      (timeOfPair (Requests.caller row.assignment).time).Bounded ∧
      Requests.Live (Requests.caller row.assignment) ∧
      (timeOfPair (Requests.caller row.assignment).time).lo + 2 < timestampBase := by
    intro row member
    obtain ⟨present, family⟩ := caller_member member
    have facts := machineClocks row present
    simp only [Trace.Row.columns, family, CircuitLayout.columns] at facts
    exact caller_clock (by omega) facts.1 facts.2
  have unique := caller_clocks_unique hp clockInverse accepted inputs
  have pool := Requests.Proofs.bounded_pool accepted.requests
    (by
      intro call present
      obtain ⟨row, member, rfl⟩ := List.mem_map.mp present
      exact clocks row member) unique
  have fulfilled := pool.1
  have bindings : ∀ row ∈ data.callers,
      Binding row.assignment before data.program ∧ PCBinding row.assignment before data.program := by
    intro row member
    obtain ⟨present, family⟩ := caller_member member
    have core := accepted.constraints row present
    simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
    have constraints := Verification.holds_of_sublist core
      (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
    exact ⟨caller_binding (by norm_num [timestampBase] at hp; omega) constraints inputs.configuration inputs.image (accepted.decoded row member),
      pc_binding (by norm_num [timestampBase] at hp; omega) pcInverse constraints inputs.configuration inputs.image (accepted.decoded row member)⟩
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
    obtain ⟨entry, present, source, address⟩ := (bindings row member).1.instruction
    refine ⟨worker, workerMember, same, entry, present, source, ?_⟩
    apply csr_injective
    exact (congrArg Requests.Request.csr same).trans address
  · intro row member
    simpa only [Requests.fulfillment, timeOfPair, rawPair, decodeTimestamp] using (workerClocks row member).1
  · intro row member
    simpa only [Requests.fulfillment, timeOfPair, rawPair, decodeTimestamp] using (workerClocks row member).2
  · exact ⟨unique, pool.2.2⟩

theorem request_binding [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestAccepted data)
    (inputs : RequestInputs data before addresses) : RequestBinding data before :=
  request_binding_checks hp clockInverse pcInverse accepted.toRequestChecks inputs

theorem unique_issued_worker [Fact p.Prime]
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    (binding : RequestBinding data before) {row : Trace.Row p PooledFamily}
    (member : row ∈ data.callers) :
    ∃! worker, worker ∈ data.workers.rows ∧ Requests.fulfillment worker = Requests.caller row.assignment := by
  exact Requests.Proofs.unique_fulfillment binding.fulfilled binding.invocations.1
    (List.mem_map.mpr ⟨row, member, rfl⟩)

theorem request_memory_execution [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : RequestAccepted data) (inputs : RequestMemoryInputs data before addresses cells) :
    RequestExecution data before cells := by
  have requests := request_binding hp clockInverse pcInverse accepted inputs.publicProgram
  have publicState : MemoryInputs data.workers before cells :=
    ⟨inputs.initialization, inputs.distinct, requests.clockRoom⟩
  exact ⟨requests, Delegation.memory_soundness hp accepted.workers publicState,
    Delegation.native_memory_execution hp accepted.workers publicState inputs.aligned⟩

end Airbender.Delegation.Caller.Proofs
