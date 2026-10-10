import Airbender.Proofs.Delegation.History

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384


private def nonzeroPort (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister index => index != 0
  | .indirect _ => true
  | _ => false

theorem port_not_zero (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.address.code row.assignment ≠ (Cell.register 0).addressCode := by
  have checked : row.ports.toList.all (fun port => nonzeroPort port.address) = true := by
    cases row with
    | mk family w => cases family <;> dsimp only [Row.ports] <;> decide
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  cases address : port.address
  all_goals simp [address, nonzeroPort] at valid
  all_goals first
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair] at valid ⊢
      exact valid
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair]

def nativeEventClock (data : MemoryData p) (event : MemoryAccess) : Nat :=
  (event.1 - memoryEpoch data) / (rawEvents data).length.succ

theorem native_clock_roundtrip {data : MemoryData p} {event : MemoryAccess}
    (positive : event.1 ≠ 0) :
    relabelMemoryEvent (nativeEventClock data)
      (relabelMemoryEvent (eventClock data) event) = event := by
  have index := List.idxOf_le_length (l := rawEvents data) (a := event)
  have clock : nativeEventClock data (relabelMemoryEvent (eventClock data) event) = event.1 := by
    simp only [nativeEventClock, relabelMemoryEvent, eventClock, if_neg positive]
    have subtraction : memoryEpoch data + (rawEvents data).length.succ * event.1 +
        (rawEvents data).idxOf event - memoryEpoch data =
        (rawEvents data).length.succ * event.1 + (rawEvents data).idxOf event := by omega
    rw [subtraction, Nat.mul_add_div (Nat.succ_pos _) event.1 _,
      Nat.div_eq_of_lt (by omega), Nat.add_zero]
  apply Prod.ext
  · exact clock
  · rfl

theorem labeled_events_split (data : MemoryData p) : labeledEvents data =
    List.append (α := MemoryAccess)
      (data.initial.map fun token => ((token.address, token.address, 0, token.value) : MemoryAccess))
      ((data.steps.map transferEvent).map (relabelMemoryEvent (eventClock data))) := by
  unfold labeledEvents rawEvents
  simp only [List.append_eq, List.map_append, List.map_map]
  congr 1

theorem native_sail_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : State),
      history.val.Perm (labeledEvents data) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells events before after ∧ SailStateMatches cells history after := by
  obtain ⟨history, permutation, consistent⟩ := labeled_history hp accepted inputs
  have initialLow : ∀ event ∈ data.initial.map (fun token =>
      ((token.address, token.address, 0, token.value) : MemoryAccess)), event.1 < memoryEpoch data := by
    intro event member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact seed_below_epoch present
  have nativeHigh : ∀ event ∈ (data.steps.map transferEvent).map
      (relabelMemoryEvent (eventClock data)), memoryEpoch data ≤ event.1 := by
    intro event member
    obtain ⟨raw, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp present
    simp only [relabelMemoryEvent, eventClock, transferEvent, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, if_false]
    omega
  have separated := permutation
  rw [labeled_events_split] at separated
  obtain ⟨events, seed, combined, native, initialized⟩ := split_memory_history _ _
    (memoryEpoch data) initialLow nativeHigh separated
  have ordered : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val) := by
    simpa only [combined] using history.property
  have online : MemoryAccessList.isConsistentOnline
      (List.append (α := MemoryAccess) events seed.val) ordered := by
    simpa only [combined] using consistent
  have source (event : MemoryAccess) (member : event ∈ events) :
      ∃ edge ∈ data.steps, event = relabelMemoryEvent (eventClock data) (transferEvent edge) := by
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp (native.mem_iff.mp member)
    obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp rawMember
    exact ⟨edge, edgeMember, rfl⟩
  have addresses (event : MemoryAccess) (member : event ∈ events) :
      ∃ cell ∈ cells, cell.addressCode = event.2.1 := by
    obtain ⟨edge, present, rfl⟩ := source event member
    exact initialized_cell hp accepted inputs present
  have zero (event : MemoryAccess) (member : event ∈ events)
      (same : event.2.1 = (Cell.register 0).addressCode) : memoryWord event.2.2.2 = 0 := by
    obtain ⟨edge, present, rfl⟩ := source event member
    obtain ⟨row, rowMember, step⟩ := List.mem_flatMap.mp present
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
    exact False.elim (port_not_zero row (by simpa using portMember) same)
  have domain : cells.Nodup := List.Nodup.of_map Cell.addressCode inputs.distinct
  obtain ⟨after, actual, final⟩ := realize_history events seed
    (initial_history_matches inputs.initialization domain seed initialized) aligned addresses zero ordered online
  let originals := events.map (relabelMemoryEvent (nativeEventClock data))
  have roundtrip : ((data.steps.map transferEvent).map (relabelMemoryEvent (eventClock data))).map
      (relabelMemoryEvent (nativeEventClock data)) = data.steps.map transferEvent := by
    rw [List.map_map]
    have pointwise (event : MemoryAccess) (member : event ∈ data.steps.map transferEvent) :
        (relabelMemoryEvent (nativeEventClock data) ∘ relabelMemoryEvent (eventClock data)) event = id event := by
      obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
      exact native_clock_roundtrip (by simp [transferEvent])
    simpa only [List.map_id] using (List.map_congr_left pointwise)
  have chronology : originals.Pairwise (fun a b => b.1 ≤ a.1) := by
    apply List.pairwise_map.mpr
    have recentSorted : MemoryAccessList.isTimestampSorted events := (List.pairwise_append.mp ordered).1
    exact recentSorted.imp (by
      intro first last earlier
      change nativeEventClock data last ≤ nativeEventClock data first
      apply Nat.div_le_div_right
      change last.1 < first.1 at earlier
      omega)
  refine ⟨history, originals, after, permutation, roundtrip ▸ native.map _, chronology,
    history_relabel (nativeEventClock data) actual, ?_⟩
  intro cell member
  simpa only [combined] using final cell member

end Airbender.Delegation.Proofs
