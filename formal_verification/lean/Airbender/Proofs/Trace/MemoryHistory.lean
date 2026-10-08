import Airbender.Review.Trace.MemoryHistory
import Airbender.Proofs.Trace.OfflineMemory

namespace Airbender.Trace.Proofs

private def retime (clock : Nat → Nat) (event : MemoryAccess) : MemoryAccess :=
  (clock event.1, event.2)

private theorem last_write_retime (clock : Nat → Nat) (events : MemoryAccessList)
    (old : events.isTimestampSorted)
    (new : MemoryAccessList.isTimestampSorted (events.map (retime clock)))
    (address : Nat) :
    MemoryAccessList.lastWriteValue (events.map (retime clock)) new address =
      MemoryAccessList.lastWriteValue events old address := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨time, key, read, write⟩ := event
    simp only [List.map_cons, retime, MemoryAccessList.lastWriteValue]
    split <;> first | rfl | exact ih _ _

/-- Clean's memory semantics depend on chronological order, not the numerical
    spacing between timestamps. No address/read/write value is changed. -/
theorem consistent_retime (clock : Nat → Nat) (events : MemoryAccessList)
    (old : events.isTimestampSorted)
    (new : MemoryAccessList.isTimestampSorted (events.map (retime clock)))
    (consistent : MemoryAccessList.isConsistentOnline events old) :
    MemoryAccessList.isConsistentOnline (events.map (retime clock)) new := by
  induction events with
  | nil => trivial
  | cons event rest ih =>
    obtain ⟨time, key, read, write⟩ := event
    change read = MemoryAccessList.lastWriteValue rest _ key ∧ _ at consistent
    change read = MemoryAccessList.lastWriteValue (rest.map (retime clock)) _ key ∧ _
    rw [last_write_retime clock rest (List.Pairwise.of_cons old) (List.Pairwise.of_cons new) key]
    exact ⟨consistent.1, ih _ _ consistent.2⟩

private theorem below_epoch [Fact p.Prime] {trace : Data p} {source : MemoryToken p}
    (member : source ∈ trace.initialMemory) : source.address < trace.memoryEpoch := by
  have present : source.address ∈ trace.initialMemory.map MemoryToken.address :=
    List.mem_map.mpr ⟨source, member, rfl⟩
  have maxBound : ∀ n ∈ trace.initialMemory.map MemoryToken.address,
      n ≤ (trace.initialMemory.map MemoryToken.address).foldr max 0 := by
    generalize trace.initialMemory.map MemoryToken.address = values
    induction values with
    | nil => simp
    | cons first rest ih =>
      intro n member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih n member).trans (Nat.le_max_right _ _)
  have bounded := maxBound _ present
  unfold Data.memoryEpoch
  omega

private theorem event_times [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    trace.nativeEvents.map Prod.fst = trace.accessTimes.map (trace.memoryEpoch + ·) := by
  simp only [MemoryAccess, Data.nativeEvents, Data.memorySteps, List.map_flatMap,
    List.map_map, Function.comp_def, Data.accessTimes]
  apply List.flatMap_congr
  intro row member
  have inputs := clock_inputs hp inverse accepted boundary row member
  simp only [Row.memorySteps, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro port portMember
  have actual : port ∈ row.ports := by simpa using portMember
  have canonical := (write_time (by omega)
    (base := rawPair row.assignment row.columns.initialTime)
    inputs.initial inputs.aligned (port_offset row port actual)).2
  exact congrArg (trace.memoryEpoch + ·) canonical

theorem memory_event_times_unique [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    (trace.memoryEvents.map Prod.fst).Nodup := by
  simp only [MemoryAccess, Data.memoryEvents, List.append_eq, List.map_append,
    List.map_map, Function.comp_def]
  apply List.nodup_append.mpr
  refine ⟨unique, ?_, ?_⟩
  · rw [event_times hp inverse accepted boundary]
    exact List.Nodup.map (by intro a b same; dsimp only at same; omega)
      (access_times_unique hp inverse accepted boundary)
  · intro a first b last equal
    obtain ⟨source, member, rfl⟩ := List.mem_map.mp first
    have below := below_epoch member
    obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp last
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp eventMember
    dsimp only at equal
    omega

private theorem sorted_events (events : MemoryAccessList) (unique : (events.map Prod.fst).Nodup) :
    ∃ history : TimestampSortedMemoryAccessList, history.val.Perm events := by
  let sorted := events.mergeSort (fun a b => decide (b.1 ≤ a.1))
  have permutation : sorted.Perm events := List.mergeSort_perm _ _
  have weak : sorted.Pairwise (fun a b => b.1 ≤ a.1) := by
    have ordered := List.pairwise_mergeSort
      (le := fun a b : MemoryAccess => decide (b.1 ≤ a.1))
      (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) events
    simpa only [decide_eq_true_eq] using ordered
  have distinct : sorted.Pairwise (fun a b => a.1 ≠ b.1) :=
    List.pairwise_map.mp ((permutation.map Prod.fst).nodup_iff.mpr unique)
  have strict : MemoryAccessList.isTimestampSorted sorted := (weak.and distinct).imp (by
    intro a b both
    change b.1 < a.1
    omega)
  exact ⟨⟨sorted, strict⟩, permutation⟩

private theorem retime_cell [Fact p.Prime] {trace : Data p} {source : MemoryToken p}
    (member : source ∈ trace.initialMemory) {history : TimestampSortedMemoryAccessList}
    (consistent : CellHistory trace source history) :
    ∃ result : TimestampSortedMemoryAccessList,
      result.val.Perm
        ((source.address, source.address, 0, source.value) ::
          (trace.memorySteps.filter fun edge => edge.1.address = source.address).map
            (fun edge => (trace.memoryEpoch + (timeOfPair edge.2.time).value,
              edge.1.address, edge.1.value, edge.2.value))) ∧
      MemoryAccessList.isConsistentOnline result.val result.property := by
  let clock := fun time => if time = 0 then source.address else trace.memoryEpoch + time - 1
  have sorted : MemoryAccessList.isTimestampSorted (history.val.map (retime clock)) := by
    apply List.pairwise_map.mpr
    apply history.property.imp
    intro first last earlier
    have below := below_epoch member
    change last.1 < first.1 at earlier
    change clock last.1 < clock first.1
    dsimp only [clock]
    split_ifs <;> omega
  refine ⟨⟨history.val.map (retime clock), sorted⟩, ?_,
    consistent_retime clock _ history.property sorted consistent.2⟩
  have mapped := consistent.1.map (retime clock)
  simpa [retime, clock, transferEvent, List.map_map, Function.comp_def] using mapped

theorem native_memory_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∃ history, MemoryHistory trace history := by
  obtain ⟨history, permutation⟩ :=
    sorted_events trace.memoryEvents (memory_event_times_unique hp inverse accepted boundary unique)
  refine ⟨history, permutation, ?_⟩
  apply (MemoryAccessList.isConsistent_iff_all_single_address _ history.property).mpr
  intro address
  let selected := MemoryAccessList.filterAddress history.val address
  have sorted := MemoryAccessList.filterAddress_sorted history.val history.property address
  have filtered := permutation.filter (fun event => decide (event.2.1 = address))
  change selected.Perm (MemoryAccessList.filterAddress trace.memoryEvents address) at filtered
  by_cases initialized : address ∈ trace.initialMemory.map MemoryToken.address
  · obtain ⟨source, member, equal⟩ := List.mem_map.mp initialized
    subst address
    obtain ⟨cellHistory, cellConsistent⟩ :=
      native_cell_histories hp inverse accepted boundary unique source member
    obtain ⟨cellHistory, projected, consistent⟩ := retime_cell member cellConsistent
    have sourceFilter := key_filter_singleton MemoryToken.address unique member
    have inputs : MemoryAccessList.filterAddress trace.memoryEvents source.address =
        (source.address, source.address, 0, source.value) ::
          (trace.memorySteps.filter fun edge => edge.1.address = source.address).map
            (fun edge => (trace.memoryEpoch + (timeOfPair edge.2.time).value,
              edge.1.address, edge.1.value, edge.2.value)) := by
      simp only [MemoryAccess, MemoryAccessList.filterAddress, Data.memoryEvents,
        Data.nativeEvents, List.append_eq, List.filter_append, List.filter_map,
        Function.comp_def, sourceFilter, List.map_singleton, List.singleton_append]
    rw [inputs] at filtered
    have same := List.Perm.eq_of_pairwise' sorted cellHistory.property
      (filtered.trans projected.symm)
    have claim := (MemoryAccessList.isConsistentSingleAddress_iff cellHistory.val source.address
      cellHistory.property (by
        simp only [List.all_eq_true]
        intro event eventMember
        have inFilter : List.Mem event (MemoryAccessList.filterAddress history.val source.address) := by
          rw [same]
          exact eventMember
        change event ∈ List.filter _ history.val at inFilter
        exact (List.mem_filter.mp inFilter).2)).mp consistent
    simpa only [same] using claim
  · have empty : MemoryAccessList.filterAddress trace.memoryEvents address = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro event member same
      have addressEq : event.2.1 = address := of_decide_eq_true same
      rcases List.mem_append.mp member with initial | native
      · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp initial
        exact initialized (List.mem_map.mpr ⟨source, sourceMember, addressEq⟩)
      · obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp native
        change edge ∈ trace.rows.flatMap Row.memorySteps at edgeMember
        obtain ⟨row, rowMember, portMember⟩ := List.mem_flatMap.mp edgeMember
        dsimp only [Row.memorySteps] at portMember
        obtain ⟨port, actualList, sameEdge⟩ := List.mem_map.mp portMember
        have actual : port ∈ row.ports := by simpa using actualList
        have origin := initialized_addresses hp inverse accepted boundary row rowMember port actual
        have sameAddress : port.address.code row.assignment = address :=
          (congrArg (fun edge : MemoryToken p × MemoryToken p => edge.1.address) sameEdge).trans addressEq
        exact initialized (sameAddress ▸ origin)
    rw [empty] at filtered
    have same : selected = [] := filtered.eq_nil
    simp only [selected] at same
    simp only [same, MemoryAccessList.isConsistentSingleAddress]

end Airbender.Trace.Proofs
