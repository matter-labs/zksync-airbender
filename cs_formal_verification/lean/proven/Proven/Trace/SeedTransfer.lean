module
public import Proven.Trace.Terminal
public import Proven.Trace.TransferHistory
public import Proven.CleanCore.Utils.OfflineMemory

@[expose] public section

/-! State-free twins of the `Transfer` history lemmas (`TransferHistory.lean`, `TransferTerminal.lean`). Those take a
    Sail `BoundaryInputs` but read only its public address domain (`addresses`, `distinct`); here the domain is
    `SeedInputs`, with no machine state, so the RV route (`RVTransfer.lean`) can use them. Proof bodies are the
    Sail ones verbatim. -/

namespace Airbender.Trace.Proofs.SeedTransfer
open Transfer (Facts rawEvents memoryEpoch eventClock labeledEvents seed_below_epoch event_clock_order
  zero_event_seed raw_seed_bound)
set_option warningAsError true
set_option maxRecDepth 16384

/-- The public seed domain of a transfer: one initial token per public cell, distinct cells. -/
structure SeedInputs (data : Transfer.Data p) (cells : List Cell) : Prop where
  addresses : (data.initial.map MemoryToken.address).Perm (cells.map Cell.addressCode)
  distinct : (cells.map Cell.addressCode).Nodup

theorem cell_histories {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
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

theorem initialized_cell {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {edge : MemoryToken p × MemoryToken p} (member : edge ∈ data.steps) :
    ∃ cell ∈ cells, cell.addressCode = edge.1.address := by
  have origin := Trace.Proofs.keyed_origins MemoryToken.address
    (fun token => (timeOfPair token.time).value) facts.matching facts.addresses facts.order edge member
  exact List.mem_map.mp (inputs.addresses.mem_iff.mp origin)

theorem raw_cell_history {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells)
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
      ite_true, List.nodup_cons] at checked
    exact checked.1 (List.mem_filter.mpr ⟨member, by simp⟩)

theorem raw_events_nodup {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
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

theorem event_clock_injective {data : Transfer.Data p}
    {cells : List Cell} (inputs : SeedInputs data cells)
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
    simp only [eventClock, ite_eq_right lastNonzero, sameTime] at equal
    have index : (rawEvents data).idxOf first = (rawEvents data).idxOf last := by omega
    exact (List.idxOf_inj firstMember).mp index

private theorem filter_address_eq (events : List MemoryAccess) (address : Nat) :
    MemoryAccessList.filterAddress events address = events.filter (fun event => decide (event.2.1 = address)) := by
  rfl

theorem labeled_history {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells) :
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

theorem raw_time_injective {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (address : first.2.1 = last.2.1)
    (time : first.1 = last.1) : first = last := by
  obtain ⟨history, permutation, _⟩ := raw_cell_history facts inputs first.2.1
  have unique : (history.val.map (fun event : MemoryAccess => event.1)).Nodup := by
    apply List.pairwise_map.mpr
    exact history.property.imp (by
      intro a b earlier
      change b.1 < a.1 at earlier
      omega)
  have projected := (permutation.map (fun event : MemoryAccess => event.1)).nodup_iff.mp unique
  apply List.inj_on_of_nodup_map projected ?_ ?_ time
  · apply List.mem_filter.mpr
    exact ⟨firstMember, by change decide (first.2.1 = first.2.1) = true; simp⟩
  · apply List.mem_filter.mpr
    exact ⟨lastMember, by change decide (last.2.1 = first.2.1) = true; simp [address]⟩

theorem event_clock_le {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (address : first.2.1 = last.2.1)
    (time : last.1 ≤ first.1) : eventClock data last ≤ eventClock data first := by
  rcases Nat.lt_or_eq_of_le time with earlier | same
  · exact Nat.le_of_lt (event_clock_order data (raw_seed_bound lastMember) earlier)
  · rw [raw_time_injective facts inputs firstMember lastMember address same.symm]

theorem terminal_path {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {sink : MemoryToken p} (member : sink ∈ data.terminal) :
    ∃ source ∈ data.initial, source.address = sink.address ∧
      ∃ path : List (MemoryToken p), path.head? = some source ∧ path.getLast? = some sink ∧
        (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
        (path.zip path.tail).Perm (data.steps.filter fun edge => edge.1.address = sink.address) := by
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    exact inputs.addresses.nodup_iff.mpr inputs.distinct
  have keys := boundary_keys MemoryToken.address facts.matching facts.addresses
  have terminalUnique := keys.nodup_iff.mp unique
  obtain ⟨source, sourceMember, address⟩ := List.mem_map.mp
    (keys.mem_iff.mpr (List.mem_map.mpr ⟨sink, member, rfl⟩))
  obtain ⟨last, lastMember, same, path, head, final, _, permutation⟩ :=
    keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      facts.matching facts.addresses unique facts.order source sourceMember
  have ordered := rank_ordered (fun token : MemoryToken p => (timeOfPair token.time).value) path
    (fun edge member => facts.order edge (List.mem_of_mem_filter (permutation.mem_iff.mp member)))
  have equal := List.inj_on_of_nodup_map terminalUnique lastMember member (same.trans address)
  subst last
  exact ⟨source, sourceMember, address, path, head, final, ordered, address ▸ permutation⟩

theorem terminal_latest_value {data : Transfer.Data p} (facts : Facts data)
    {cells : List Cell} (inputs : SeedInputs data cells)
    {history : TimestampSortedMemoryAccessList} (bound : history.val.Perm (labeledEvents data))
    {sink : MemoryToken p} (member : sink ∈ data.terminal) :
    MemoryAccessList.lastWriteValue history.val history.property sink.address = sink.value := by
  obtain ⟨source, sourceMember, address, path, head, final, ordered, permutation⟩ :=
    terminal_path facts inputs member
  let rank := fun token : MemoryToken p => (timeOfPair token.time).value
  have upper : ∀ token ∈ path, rank token ≤ rank sink := by
    intro token present
    have weak := ordered.imp Nat.le_of_lt
    have last := weak.rel_getLast (List.mem_map.mpr ⟨token, present, rfl⟩)
    have finalRank : (path.map rank).getLast? = some (rank sink) := by
      rw [List.getLast?_map, final]
      rfl
    change rank token ≤ (path.map rank).getLast _ at last
    rw [List.getLast_of_getLast?_eq_some finalRank] at last
    exact last
  have writeUpper : ∀ edge ∈ data.steps, edge.1.address = sink.address → rank edge.2 ≤ rank sink := by
    intro edge present same
    have onPath := permutation.mem_iff.mpr (List.mem_filter.mpr ⟨present, by simpa using same⟩)
    exact upper edge.2 (List.mem_of_mem_tail (List.of_mem_zip onPath).2)
  have tokenPresent := facts.matching.mem_iff.mpr (List.mem_append_left _ member)
  rcases List.mem_append.mp tokenPresent with initial | native
  · have unique : (data.initial.map MemoryToken.address).Nodup := by
      exact inputs.addresses.nodup_iff.mpr inputs.distinct
    have same := List.inj_on_of_nodup_map unique initial sourceMember address.symm
    subst sink
    have noNative : ∀ edge ∈ data.steps, edge.1.address ≠ source.address := by
      intro edge present equal
      have onPath := permutation.mem_iff.mpr (List.mem_filter.mpr ⟨present, by simpa using equal⟩)
      have increasing := List.pairwise_map.mp ordered
      have first := (increasing.imp (fun {_ _} h => Nat.le_of_lt h)).rel_head (List.of_mem_zip onPath).1
      have firstBound : rank source ≤ rank edge.1 := by
        simpa only [List.head_of_head?_eq_some head] using first
      have lastBound := writeUpper edge present equal
      have growth := facts.order edge present
      change rank edge.1 < rank edge.2 at growth
      omega
    let raw : MemoryAccess := (0, source.address, 0, source.value)
    have present : raw ∈ rawEvents data := List.mem_append_left _
      (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
    have recent : List.Mem (relabelMemoryEvent (eventClock data) raw) history.val :=
      bound.mem_iff.mpr (List.mem_map.mpr ⟨raw, present, rfl⟩)
    apply last_write_max history.val history.property (event := relabelMemoryEvent (eventClock data) raw) recent
    intro other otherMember sameAddress
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp (bound.mem_iff.mp otherMember)
    rcases List.mem_append.mp oldMember with initial | native
    · obtain ⟨token, tokenMember, rfl⟩ := List.mem_map.mp initial
      change token.address = source.address at sameAddress
      simpa [eventClock, raw, relabelMemoryEvent] using Nat.le_of_eq sameAddress
    · obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp native
      exact False.elim (noNative edge edgeMember sameAddress)
  · obtain ⟨edge, edgeMember, written⟩ := List.mem_map.mp native
    let raw := transferEvent edge
    have present : raw ∈ rawEvents data := List.mem_append_right _ (List.mem_map.mpr ⟨edge, edgeMember, rfl⟩)
    have recent : List.Mem (relabelMemoryEvent (eventClock data) raw) history.val :=
      bound.mem_iff.mpr (List.mem_map.mpr ⟨raw, present, rfl⟩)
    have code : raw.2.1 = sink.address := (facts.addresses edge edgeMember).trans (congrArg MemoryToken.address written)
    have value : raw.2.2.2 = sink.value := congrArg MemoryToken.value written
    rw [← code, ← value]
    apply last_write_max history.val history.property recent
    intro other otherMember sameAddress
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp (bound.mem_iff.mp otherMember)
    apply event_clock_le facts inputs present oldMember sameAddress.symm
    rcases List.mem_append.mp oldMember with initial | native
    · obtain ⟨token, _, rfl⟩ := List.mem_map.mp initial
      exact Nat.zero_le _
    · obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.mp native
      have same : prior.1.address = sink.address := sameAddress.trans code
      have less := writeUpper prior priorMember same
      change rank prior.2 + 1 ≤ rank edge.2 + 1
      rw [written]
      omega

end Airbender.Trace.Proofs.SeedTransfer
