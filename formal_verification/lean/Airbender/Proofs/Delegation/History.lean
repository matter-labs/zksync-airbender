import Airbender.Proofs.Delegation.Memory
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.NativeSailHistory

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384


def rawEvents (data : MemoryData p) : List MemoryAccess :=
  List.append (α := MemoryAccess)
    (data.initial.map fun token => (0, token.address, 0, token.value))
    (data.steps.map transferEvent)

def memoryEpoch (data : MemoryData p) : Nat :=
  (data.initial.map MemoryToken.address).foldr max 0 + 1

def eventClock (data : MemoryData p) (event : MemoryAccess) : Nat :=
  if event.1 = 0 then event.2.1 else
    memoryEpoch data + (rawEvents data).length.succ * event.1 + (rawEvents data).idxOf event

def labeledEvents (data : MemoryData p) : List MemoryAccess :=
  (rawEvents data).map (Trace.Proofs.relabelMemoryEvent (eventClock data))

theorem seed_below_epoch {data : MemoryData p} {source : MemoryToken p}
    (member : source ∈ data.initial) : source.address < memoryEpoch data := by
  have maxBound : ∀ n ∈ data.initial.map MemoryToken.address,
      n ≤ (data.initial.map MemoryToken.address).foldr max 0 := by
    generalize data.initial.map MemoryToken.address = values
    induction values with
    | nil => simp
    | cons first rest ih =>
      intro n member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih n member).trans (Nat.le_max_right _ _)
  have bound := maxBound source.address (List.mem_map.mpr ⟨source, member, rfl⟩)
  exact Nat.lt_succ_of_le bound

theorem event_clock_order (data : MemoryData p) {first last : MemoryAccess}
    (lastBound : last.1 = 0 → last.2.1 < memoryEpoch data)
    (earlier : last.1 < first.1) : eventClock data last < eventClock data first := by
  have firstPositive : first.1 ≠ 0 := by omega
  have lastIndex := List.idxOf_le_length (l := rawEvents data) (a := last)
  have firstIndex := List.idxOf_le_length (l := rawEvents data) (a := first)
  simp only [eventClock, if_neg firstPositive]
  by_cases zero : last.1 = 0
  · rw [if_pos zero]
    have bound := lastBound zero
    omega
  · rw [if_neg zero]
    have multiplied := Nat.mul_le_mul_left (rawEvents data).length.succ
      (Nat.succ_le_of_lt earlier)
    simp only [Nat.mul_succ] at multiplied
    omega

theorem initialized_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.steps) :
    ∃ cell ∈ cells, cell.addressCode = edge.1.address := by
  have origin := Trace.Proofs.keyed_origins MemoryToken.address
    (fun token => (timeOfPair token.time).value) accepted.matching preserved_addresses
    (memory_order hp accepted inputs) edge member
  rw [Trace.Proofs.image_addresses inputs.initialization] at origin
  exact List.mem_map.mp origin

theorem zero_event_seed {data : MemoryData p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) (zero : event.1 = 0) :
    ∃ source ∈ data.initial, event = (0, source.address, 0, source.value) := by
  rcases List.mem_append.mp member with initial | native
  · obtain ⟨source, present, rfl⟩ := List.mem_map.mp initial
    exact ⟨source, present, rfl⟩
  · obtain ⟨edge, _, rfl⟩ := List.mem_map.mp native
    simp [transferEvent] at zero

theorem raw_cell_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    (address : Nat) : ∃ history : TimestampSortedMemoryAccessList,
      history.val.Perm (MemoryAccessList.filterAddress (rawEvents data) address) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    rw [Trace.Proofs.image_addresses inputs.initialization]
    exact inputs.distinct
  by_cases initialized : address ∈ data.initial.map MemoryToken.address
  · obtain ⟨source, present, rfl⟩ := List.mem_map.mp initialized
    obtain ⟨history, permutation, consistent⟩ := cell_histories hp accepted inputs source present
    have sourceFilter := Trace.Proofs.key_filter_singleton MemoryToken.address unique present
    have same : MemoryAccessList.filterAddress (rawEvents data) source.address =
        (0, source.address, 0, source.value) ::
          (data.steps.filter fun edge => edge.1.address = source.address).map transferEvent := by
      simp only [MemoryAccessList.filterAddress, rawEvents, List.append_eq, List.filter_append,
        List.filter_map, Function.comp_def, sourceFilter, List.map_singleton, List.singleton_append]
      rfl
    exact ⟨history, same ▸ permutation, consistent⟩
  · have empty : MemoryAccessList.filterAddress (rawEvents data) address = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro event member same
      have equal : event.2.1 = address := of_decide_eq_true same
      rcases List.mem_append.mp member with initial | native
      · obtain ⟨source, present, rfl⟩ := List.mem_map.mp initial
        exact initialized (List.mem_map.mpr ⟨source, present, equal⟩)
      · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp native
        have origin := Trace.Proofs.keyed_origins MemoryToken.address
          (fun token => (timeOfPair token.time).value) accepted.matching preserved_addresses
          (memory_order hp accepted inputs) edge present
        exact initialized (equal ▸ origin)
    refine ⟨⟨[], by simp [MemoryAccessList.isTimestampSorted]⟩, ?_, trivial⟩
    rw [empty]

theorem raw_seed_bound {data : MemoryData p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) : event.1 = 0 → event.2.1 < memoryEpoch data := by
  intro zero
  obtain ⟨source, present, rfl⟩ := zero_event_seed member zero
  exact seed_below_epoch present

private theorem nodup_of_address_filters (events : List MemoryAccess)
    (unique : ∀ address, (MemoryAccessList.filterAddress events address).Nodup) : events.Nodup := by
  induction events with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨time, key, old, value⟩ := head
    have tailUnique (address : Nat) : (MemoryAccessList.filterAddress rest address).Nodup := by
      have checked := unique address
      by_cases same : key = address
      · simp [MemoryAccessList.filterAddress, same] at checked
        exact checked.2
      · simpa [MemoryAccessList.filterAddress, same] using checked
    refine List.nodup_cons.mpr ⟨?_, ih tailUnique⟩
    intro member
    have checked := unique key
    simp only [MemoryAccessList.filterAddress, List.filter_cons, decide_true,
      if_true, List.nodup_cons] at checked
    exact checked.1 (List.mem_filter.mpr ⟨member, by simp⟩)

theorem raw_events_nodup [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    (rawEvents data).Nodup := by
  apply nodup_of_address_filters
  intro address
  obtain ⟨history, permutation, _⟩ := raw_cell_history hp accepted inputs address
  have distinct : history.val.Nodup := history.property.imp (by
    intro a b earlier equal
    subst b
    change a.1 < a.1 at earlier
    omega)
  exact permutation.nodup_iff.mp distinct

theorem event_clock_injective [Fact p.Prime] {data : MemoryData p}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (equal : eventClock data first = eventClock data last) :
    first = last := by
  have sameTime : first.1 = last.1 := by
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with earlier | earlier
    · have less := event_clock_order data (raw_seed_bound firstMember) earlier
      rw [equal] at less
      omega
    · have less := event_clock_order data (raw_seed_bound lastMember) earlier
      rw [equal] at less
      omega
  by_cases zero : first.1 = 0
  · have lastZero : last.1 = 0 := sameTime ▸ zero
    obtain ⟨source, present, rfl⟩ := zero_event_seed firstMember zero
    obtain ⟨sink, sinkMember, rfl⟩ := zero_event_seed lastMember lastZero
    have unique : (data.initial.map MemoryToken.address).Nodup := by
      rw [Trace.Proofs.image_addresses inputs.initialization]
      exact inputs.distinct
    have address : source.address = sink.address := by simpa [eventClock] using equal
    have same := List.inj_on_of_nodup_map unique present sinkMember address
    rw [same]
  · have lastNonzero : last.1 ≠ 0 := by omega
    simp only [eventClock, if_neg lastNonzero, sameTime] at equal
    have index : (rawEvents data).idxOf first = (rawEvents data).idxOf last := by omega
    exact (List.idxOf_inj firstMember).mp index

private theorem filter_address_eq (events : List MemoryAccess) (address : Nat) :
    MemoryAccessList.filterAddress events address = events.filter (fun event => decide (event.2.1 = address)) := by
  rfl

theorem labeled_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : MemoryInputs data before cells) :
    ∃ history : TimestampSortedMemoryAccessList, history.val.Perm (labeledEvents data) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  have unique : ((labeledEvents data).map (fun event : MemoryAccess => event.1)).Nodup := by
    rw [labeledEvents, List.map_map]
    change ((rawEvents data).map (eventClock data)).Nodup
    exact List.Nodup.map_on
      (fun _ first _ last equal => event_clock_injective inputs first last equal)
      (raw_events_nodup hp accepted inputs)
  obtain ⟨history, permutation⟩ := Trace.Proofs.sorted_events _ unique
  refine ⟨history, permutation, ?_⟩
  apply (MemoryAccessList.isConsistent_iff_all_single_address _ history.property).mpr
  intro address
  obtain ⟨original, originalPerm, originalConsistent⟩ := raw_cell_history hp accepted inputs address
  have rawMember {event : MemoryAccess} (member : List.Mem (α := MemoryAccess) event original.val) : event ∈ rawEvents data :=
    List.mem_of_mem_filter (originalPerm.mem_iff.mp member)
  have sorted : MemoryAccessList.isTimestampSorted
      (original.val.map (Trace.Proofs.relabelMemoryEvent (eventClock data))) := by
    apply List.pairwise_map.mpr
    exact original.property.imp_of_mem (fun first last earlier =>
      event_clock_order data (raw_seed_bound (rawMember last)) earlier)
  let projected : TimestampSortedMemoryAccessList :=
    ⟨original.val.map (Trace.Proofs.relabelMemoryEvent (eventClock data)), sorted⟩
  have consistent := Trace.Proofs.consistent_relabel (eventClock data) original.val
    original.property sorted originalConsistent
  have projectedPerm : projected.val.Perm
      (MemoryAccessList.filterAddress (labeledEvents data) address) := by
    have mapped := originalPerm.map (Trace.Proofs.relabelMemoryEvent (eventClock data))
    dsimp only [projected]
    unfold labeledEvents
    rw [filter_address_eq, List.filter_map]
    rw [filter_address_eq] at mapped
    convert mapped using 1
    congr 1
  have filtered := permutation.filter (fun event => decide (event.2.1 = address))
  have same : MemoryAccessList.filterAddress history.val address = projected.val :=
    List.Perm.eq_of_pairwise' (MemoryAccessList.filterAddress_sorted _ history.property address)
      projected.property (filtered.trans projectedPerm.symm)
  have claim := (MemoryAccessList.isConsistentSingleAddress_iff projected.val address
    projected.property (by
      simp only [List.all_eq_true]
      intro event member
      have selected := projectedPerm.mem_iff.mp member
      exact (List.mem_filter.mp selected).2)).mp consistent
  simpa only [same] using claim

end Airbender.Delegation.Proofs
