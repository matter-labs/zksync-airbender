import Slop.Trace.NativeSailHistory
import Slop.Trace.OfflineMemory

namespace Airbender.Trace.Proofs.Transfer
open Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

structure Data (p : Nat) where
  initial : List (MemoryToken p)
  terminal : List (MemoryToken p)
  steps : List (MemoryToken p × MemoryToken p)

structure Facts (data : Data p) : Prop where
  matching : (data.initial ++ data.steps.map Prod.snd).Perm
    (data.terminal ++ data.steps.map Prod.fst)
  addresses : ∀ edge ∈ data.steps, edge.1.address = edge.2.address
  order : ∀ edge ∈ data.steps,
    (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value

structure Inputs (data : Data p) (before : State) (cells : List Cell) : Prop where
  initialization : initialImage before cells = some data.initial
  distinct : (cells.map Cell.addressCode).Nodup

structure BoundaryInputs (data : Data p) (before : State) (cells : List Cell) : Prop where
  addresses : (data.initial.map MemoryToken.address).Perm (cells.map Cell.addressCode)
  distinct : (cells.map Cell.addressCode).Nodup
  reads : ∀ token ∈ data.initial, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.read before = .ok (memoryWord token.value) before

def Inputs.toBoundaryInputs {data : Data p} {before : State} {cells : List Cell}
    (inputs : Inputs data before cells) : BoundaryInputs data before cells := by
  refine ⟨?_, inputs.distinct, ?_⟩
  · rw [image_addresses inputs.initialization]
  · intro token member
    obtain ⟨cell, present, value, read, equal⟩ := image_sources inputs.initialization token member
    refine ⟨cell, present, ?_, ?_⟩
    · rw [equal]; rfl
    · rw [equal]
      simp only [Cell.initialToken, memoryWord, Nat.unpair_pair]
      change cell.read before = .ok (Arithmetic.Word.ofBitVec value).toBitVec before
      rw [Arithmetic.Word.ofBitVec_roundtrip]
      exact read

theorem boundary_history_matches {data : Data p} {before : State} {cells : List Cell}
    (inputs : BoundaryInputs data before cells) (seed : TimestampSortedMemoryAccessList)
    (permutation : seed.val.Perm
      (data.initial.map fun token => (token.address, token.address, 0, token.value))) :
    SailStateMatches cells seed before := by
  apply seed_history_matches (inputs.addresses.nodup_iff.mpr inputs.distinct) ?_ seed permutation
  intro cell member
  obtain ⟨token, present, address⟩ := List.mem_map.mp (inputs.addresses.mem_iff.mpr
    (List.mem_map.mpr ⟨cell, member, rfl⟩))
  obtain ⟨actual, _, equal, read⟩ := inputs.reads token present
  have same : actual = cell := cell_address_injective (equal.trans address)
  subst actual
  exact ⟨token, present, address, read⟩

theorem cell_histories {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∀ source ∈ data.initial, ∃ history : TimestampSortedMemoryAccessList,
      history.val.Perm ((0, source.address, 0, source.value) ::
        (data.steps.filter fun edge => edge.1.address = source.address).map transferEvent) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    exact inputs.addresses.nodup_iff.mpr inputs.distinct
  intro source member
  obtain ⟨_, _, _, path, head, _, _, permutation⟩ :=
    keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      facts.matching facts.addresses unique facts.order source member
  have ordered := rank_ordered (fun token : MemoryToken p => (timeOfPair token.time).value) path
    (fun edge member => facts.order edge (List.mem_of_mem_filter (permutation.mem_iff.mp member)))
  exact cell_history_of_path data.steps source path head ordered permutation

def rawEvents (data : Data p) : List MemoryAccess :=
  List.append (α := MemoryAccess)
    (data.initial.map fun token => (0, token.address, 0, token.value))
    (data.steps.map transferEvent)

def memoryEpoch (data : Data p) : Nat :=
  (data.initial.map MemoryToken.address).foldr max 0 + 1

def eventClock (data : Data p) (event : MemoryAccess) : Nat :=
  if event.1 = 0 then event.2.1 else
    memoryEpoch data + (rawEvents data).length.succ * event.1 + (rawEvents data).idxOf event

def labeledEvents (data : Data p) : List MemoryAccess :=
  (rawEvents data).map (Trace.Proofs.relabelMemoryEvent (eventClock data))

theorem seed_below_epoch {data : Data p} {source : MemoryToken p}
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

theorem event_clock_order (data : Data p) {first last : MemoryAccess}
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

theorem initialized_cell {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.steps) :
    ∃ cell ∈ cells, cell.addressCode = edge.1.address := by
  have origin := Trace.Proofs.keyed_origins MemoryToken.address
    (fun token => (timeOfPair token.time).value) facts.matching facts.addresses facts.order edge member
  exact List.mem_map.mp (inputs.addresses.mem_iff.mp origin)

theorem zero_event_seed {data : Data p} {event : MemoryAccess}
    (member : event ∈ rawEvents data) (zero : event.1 = 0) :
    ∃ source ∈ data.initial, event = (0, source.address, 0, source.value) := by
  rcases List.mem_append.mp member with initial | native
  · obtain ⟨source, present, rfl⟩ := List.mem_map.mp initial
    exact ⟨source, present, rfl⟩
  · obtain ⟨edge, _, rfl⟩ := List.mem_map.mp native
    simp [transferEvent] at zero

theorem raw_cell_history {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    (address : Nat) : ∃ history : TimestampSortedMemoryAccessList,
      history.val.Perm (MemoryAccessList.filterAddress (rawEvents data) address) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    exact inputs.addresses.nodup_iff.mpr inputs.distinct
  by_cases initialized : address ∈ data.initial.map MemoryToken.address
  · obtain ⟨source, present, rfl⟩ := List.mem_map.mp initialized
    obtain ⟨history, permutation, consistent⟩ := cell_histories facts inputs source present
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
          (fun token => (timeOfPair token.time).value) facts.matching facts.addresses facts.order edge present
        exact initialized (equal ▸ origin)
    refine ⟨⟨[], by simp [MemoryAccessList.isTimestampSorted]⟩, ?_, trivial⟩
    rw [empty]

private theorem address_clocks_distinct (events : List MemoryAccess)
    (perAddress : ∀ address, ((events.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup) :
    (events.map fun event => (event.1, event.2.1)).Nodup := by
  induction events with
  | nil => simp
  | cons first rest ih =>
    have tailLocal : ∀ address,
        ((rest.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup := by
      intro address
      have unique := perAddress address
      by_cases same : first.2.1 = address
      · simp only [List.filter_cons, same, decide_true, if_true] at unique
        change (first.1 :: (rest.filter fun event => decide (event.2.1 = address)).map Prod.fst).Nodup at unique
        exact (List.nodup_cons.mp unique).2
      · simpa [same] using unique
    refine List.nodup_cons.mpr ⟨?_, ih tailLocal⟩
    intro present
    obtain ⟨other, member, equal⟩ := List.mem_map.mp present
    change (other.1, other.2.1) = (first.1, first.2.1) at equal
    have sameTime := (Prod.mk.inj equal).1
    have sameAddress := (Prod.mk.inj equal).2
    have unique := perAddress first.2.1
    have excluded : first.1 ∉ (rest.filter fun event => decide (event.2.1 = first.2.1)).map Prod.fst := by
      simp only [List.filter_cons, decide_true, if_true] at unique
      change (first.1 :: (rest.filter fun event => decide (event.2.1 = first.2.1)).map Prod.fst).Nodup at unique
      exact (List.nodup_cons.mp unique).1
    exact excluded (List.mem_map.mpr ⟨other,
      List.mem_filter.mpr ⟨member, by simpa only [decide_eq_true_eq] using sameAddress⟩,
      sameTime⟩)

theorem raw_address_clocks_distinct {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ((rawEvents data).map fun event => (event.1, event.2.1)).Nodup := by
  apply address_clocks_distinct
  intro address
  obtain ⟨history, permutation, _⟩ := raw_cell_history facts inputs address
  have unique : (history.val.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact history.property.imp (by
      intro a b less equal
      change b.1 < a.1 at less
      omega)
  exact (permutation.map Prod.fst).nodup_iff.mp unique

theorem raw_seed_bound {data : Data p} {event : MemoryAccess}
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

theorem raw_events_nodup {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    (rawEvents data).Nodup := by
  apply nodup_of_address_filters
  intro address
  obtain ⟨history, permutation, _⟩ := raw_cell_history facts inputs address
  have distinct : history.val.Nodup := history.property.imp (by
    intro a b earlier equal
    subst b
    change a.1 < a.1 at earlier
    omega)
  exact permutation.nodup_iff.mp distinct

theorem event_clock_injective {data : Data p}
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
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
      exact inputs.addresses.nodup_iff.mpr inputs.distinct
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

theorem labeled_history {data : Data p} (facts : Facts data)
    {before : Reference.RiscV.Sail.State} {cells : List Cell} (inputs : BoundaryInputs data before cells) :
    ∃ history : TimestampSortedMemoryAccessList, history.val.Perm (labeledEvents data) ∧
      MemoryAccessList.isConsistentOnline history.val history.property := by
  have unique : ((labeledEvents data).map (fun event : MemoryAccess => event.1)).Nodup := by
    rw [labeledEvents, List.map_map]
    change ((rawEvents data).map (eventClock data)).Nodup
    exact List.Nodup.map_on
      (fun _ first _ last equal => event_clock_injective inputs first last equal)
      (raw_events_nodup facts inputs)
  obtain ⟨history, permutation⟩ := Trace.Proofs.sorted_events _ unique
  refine ⟨history, permutation, ?_⟩
  apply (MemoryAccessList.isConsistent_iff_all_single_address _ history.property).mpr
  intro address
  obtain ⟨original, originalPerm, originalConsistent⟩ := raw_cell_history facts inputs address
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

def nativeEventClock (data : Data p) (event : MemoryAccess) : Nat :=
  (event.1 - memoryEpoch data) / (rawEvents data).length.succ

theorem native_clock_roundtrip {data : Data p} {event : MemoryAccess}
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

theorem labeled_events_split (data : Data p) : labeledEvents data =
    List.append (α := MemoryAccess)
      (data.initial.map fun token => ((token.address, token.address, 0, token.value) : MemoryAccess))
      ((data.steps.map transferEvent).map (relabelMemoryEvent (eventClock data))) := by
  unfold labeledEvents rawEvents
  simp only [List.append_eq, List.map_append, List.map_map]
  congr 1

theorem native_sail_history_at_boundary {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : BoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : State),
      history.val.Perm (labeledEvents data) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells events before after ∧ SailStateMatches cells history after := by
  obtain ⟨history, permutation, consistent⟩ := labeled_history facts inputs
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
    exact initialized_cell facts inputs present
  have zeroEvents (event : MemoryAccess) (member : event ∈ events)
      (same : event.2.1 = (Cell.register 0).addressCode) : memoryWord event.2.2.2 = 0 := by
    obtain ⟨edge, present, rfl⟩ := source event member
    exact zero edge present same
  obtain ⟨after, actual, final⟩ := realize_history events seed
    (boundary_history_matches inputs seed initialized) aligned addresses zeroEvents ordered online
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

theorem native_sail_history {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : Inputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : State),
      history.val.Perm (labeledEvents data) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      SailHistory cells events before after ∧ SailStateMatches cells history after :=
  native_sail_history_at_boundary facts inputs.toBoundaryInputs aligned zero

end Airbender.Trace.Proofs.Transfer
