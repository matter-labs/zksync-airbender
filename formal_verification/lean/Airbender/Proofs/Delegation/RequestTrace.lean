import Airbender.Review.Delegation.Theorems
import Airbender.Review.Delegation.RequestTrace
import Airbender.Proofs.Delegation.CallerPC
import Airbender.Proofs.Trace.Pooled
import Airbender.Proofs.Trace.StateClocks

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

theorem request_binding [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (pcInverse : (-30720 : ZMod p) * 65536 = 1)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} (accepted : RequestAccepted data)
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
  have live : ∀ request ∈ data.calls, Requests.Live request := by
    intro request member
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
    exact (clocks row present).2.1
  have allCalls : data.calls.filter (fun request => decide (Requests.Live request)) = data.calls := by
    apply List.filter_eq_self.mpr
    intro request member
    exact decide_eq_true (live request member)
  have fulfilled := Requests.Proofs.nonzero_matching accepted.requests
  rw [allCalls] at fulfilled
  have bindings : ∀ row ∈ data.callers,
      Binding row.assignment before data.program ∧ PCBinding row.assignment before data.program := by
    intro row member
    obtain ⟨present, family⟩ := caller_member member
    have core := accepted.constraints row present
    simp only [Trace.Row.constraints, family, CircuitLayout.constraints] at core
    have constraints := Verification.holds_of_sublist core
      (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
    exact ⟨caller_binding (by norm_num [timestampBase] at hp; omega) constraints inputs.image (accepted.decoded row member),
      pc_binding (by norm_num [timestampBase] at hp; omega) pcInverse constraints inputs.image (accepted.decoded row member)⟩
  have workerClocks : ∀ row ∈ data.workers.rows,
      (timeOfPair (Requests.fulfillment row).time).Bounded ∧
      (timeOfPair (Requests.fulfillment row).time).lo + 2 < timestampBase := by
    intro worker present
    by_cases zero : (Requests.fulfillment worker).time = (0, 0)
    · rw [zero]
      norm_num [timeOfPair, Timestamp.Bounded, timestampBase]
    · have member : Requests.fulfillment worker ∈ data.fulfillments.filter (fun request => decide (Requests.Live request)) :=
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨worker, present, rfl⟩, decide_eq_true zero⟩
      have inCalls := fulfilled.mem_iff.mpr member
      obtain ⟨row, rowMember, same⟩ := List.mem_map.mp inCalls
      rw [← same]
      exact ⟨(clocks row rowMember).1, (clocks row rowMember).2.2⟩
  refine ⟨bindings, fulfilled, ?_, ?_, ?_⟩
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
