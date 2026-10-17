import Airbender.Review.Helpers.Memory.Projection
import Airbender.Proofs.Trace.NativeSailHistory

namespace Airbender.Trace.Proofs

/-- Erasing other addresses does not change the newest write of a kept address.
    Selecting individual events at one address would not have this property. -/
theorem last_write_project (keep : Nat → Bool) (events : MemoryAccessList)
    (sorted : events.isTimestampSorted) (address : Nat) (selected : keep address = true) :
    MemoryAccessList.lastWriteValue (events.filter fun event => keep event.2.1)
      (sorted.filter _) address = MemoryAccessList.lastWriteValue events sorted address := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    obtain ⟨time, key, read, write⟩ := event
    by_cases same : key = address
    · subst key
      simp [selected, MemoryAccessList.lastWriteValue]
    · cases kept : keep key <;>
        simp [kept, MemoryAccessList.lastWriteValue, same, ih (List.Pairwise.of_cons sorted)]

/-- Whole-address projection preserves Clean's original online consistency. -/
theorem consistent_project (keep : Nat → Bool) (events : MemoryAccessList)
    (sorted : events.isTimestampSorted)
    (consistent : MemoryAccessList.isConsistentOnline events sorted) :
    MemoryAccessList.isConsistentOnline (events.filter fun event => keep event.2.1)
      (sorted.filter _) := by
  induction events with
  | nil => trivial
  | cons event rest ih =>
    obtain ⟨time, key, read, write⟩ := event
    change read = MemoryAccessList.lastWriteValue rest _ key ∧ _ at consistent
    cases kept : keep key
    · simpa only [List.filter_cons, kept, Bool.false_eq_true, ↓reduceIte] using
        ih (List.Pairwise.of_cons sorted) consistent.2
    · simp only [List.filter_cons, kept, ↓reduceIte]
      constructor
      · exact consistent.1.trans (last_write_project keep rest
          (List.Pairwise.of_cons sorted) key kept).symm
      · exact ih (List.Pairwise.of_cons sorted) consistent.2

/-- A state realizing kept cells need not realize any erased native cell. -/
theorem matches_project {cells : List Cell} {history : TimestampSortedMemoryAccessList}
    {state : Reference.RiscV.Sail.State} (keep : Nat → Bool)
    (selected : ∀ cell ∈ cells, keep cell.addressCode = true) :
    SailStateMatches cells (projectHistory keep history) state ↔
      SailStateMatches cells history state := by
  constructor <;> intro bound cell member
  · have read := bound cell member
    have same : MemoryAccessList.lastWriteValue (projectHistory keep history).val
        (projectHistory keep history).property cell.addressCode =
        MemoryAccessList.lastWriteValue history.val history.property cell.addressCode :=
      last_write_project keep history.val history.property _ (selected cell member)
    rw [same] at read
    exact read
  · have same : MemoryAccessList.lastWriteValue (projectHistory keep history).val
        (projectHistory keep history).property cell.addressCode =
        MemoryAccessList.lastWriteValue history.val history.property cell.addressCode :=
      last_write_project keep history.val history.property _ (selected cell member)
    change cell.read state = .ok (memoryWord _) state
    rw [same]
    exact bound cell member

/-- Realize only retained native addresses in Sail. The full original Clean
    history remains checked, including every erased seed and native access. -/
theorem projected_native_sail_history {Kind : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime] [ClockLaws Kind p] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p Kind} (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup)
    (keep : Nat → Bool) {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells =
      some (trace.initialMemory.filter fun token => keep token.address))
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (selected : ∀ cell ∈ cells, keep cell.addressCode = true)
    (addresses : ∀ event ∈ trace.nativeEvents, keep event.2.1 = true →
      ∃ cell ∈ cells, cell.addressCode = event.2.1)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ events.Perm trace.nativeEvents ∧
      MemoryAccessList.isTimestampSorted events ∧
      SailHistory cells (events.filter fun event => keep event.2.1) before after ∧
      SailStateMatches cells history after := by
  obtain ⟨history, checked⟩ := native_memory_history hp accepted boundary unique
  obtain ⟨events, seed, combined, permutation, initial⟩ := native_history_parts checked
  let projectedSeed := projectHistory keep seed
  have initialSelected : projectedSeed.val.Perm
      ((trace.initialMemory.filter fun token => keep token.address).map fun token =>
        (token.address, token.address, 0, token.value)) := by
    simpa only [projectedSeed, projectHistory, List.filter_map, Function.comp_def] using
      initial.filter (fun event => keep event.2.1)
  have selectedCombined : List.append (α := MemoryAccess)
      (events.filter fun event => keep event.2.1) projectedSeed.val =
      (projectHistory keep history).val := by
    change _ = history.val.filter _
    rw [← combined]
    simp only [List.append_eq, List.filter_append, projectedSeed, projectHistory]
  have sorted : MemoryAccessList.isTimestampSorted
      (List.append (α := MemoryAccess) (events.filter fun event => keep event.2.1) projectedSeed.val) := by
    rw [selectedCombined]
    exact (projectHistory keep history).property
  have consistent : MemoryAccessList.isConsistentOnline
      (List.append (α := MemoryAccess) (events.filter fun event => keep event.2.1) projectedSeed.val) sorted := by
    have projected : MemoryAccessList.isConsistentOnline (projectHistory keep history).val
        (projectHistory keep history).property :=
      consistent_project keep history.val history.property checked.2
    simpa only [selectedCombined] using projected
  obtain ⟨after, actual, final⟩ := realize_history _ projectedSeed
    (initial_history_matches image domain projectedSeed initialSelected) aligned
    (fun event member => addresses event (permutation.mem_iff.mp (List.mem_filter.mp member).1)
      (List.mem_filter.mp member).2)
    (fun event member => zero event (permutation.mem_iff.mp (List.mem_filter.mp member).1))
    sorted consistent
  refine ⟨history, events, after, checked, permutation, ?_, actual, ?_⟩
  · have ordered : MemoryAccessList.isTimestampSorted
        (List.append (α := MemoryAccess) events seed.val) := by
      simpa only [combined] using history.property
    exact (List.pairwise_append.mp ordered).1
  · apply (matches_project keep selected).mp
    intro cell member
    simpa only [selectedCombined] using final cell member

end Airbender.Trace.Proofs
