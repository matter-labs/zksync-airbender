import Airbender.Proofs.Trace.NativeSailHistory

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail

private theorem last_write_max (history : MemoryAccessList)
    (sorted : history.isTimestampSorted) {event : MemoryAccess}
    (member : List.Mem event history)
    (latest : ∀ other : MemoryAccess, List.Mem other history →
      other.2.1 = event.2.1 → other.1 ≤ event.1) :
    MemoryAccessList.lastWriteValue history sorted event.2.1 = event.2.2.2 := by
  induction history with
  | nil => cases member
  | cons head rest ih =>
    obtain ⟨time, key, old, value⟩ := head
    rcases List.mem_cons.mp member with rfl | member
    · simp [MemoryAccessList.lastWriteValue]
    · have different : key ≠ event.2.1 := by
        intro equal
        have greater := (List.pairwise_cons.mp sorted).1 event member
        have less := latest (time, key, old, value) (List.mem_cons_self) equal
        change event.1 < time at greater
        change time ≤ event.1 at less
        omega
      simpa only [MemoryAccessList.lastWriteValue, if_neg different] using
        ih (List.Pairwise.of_cons sorted) member
          (fun other present => latest other (List.mem_cons_of_mem _ present))

private theorem terminal_path [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup)
    {sink : MemoryToken p} (member : sink ∈ trace.terminalMemory) :
    ∃ source ∈ trace.initialMemory, ∃ path : List (MemoryToken p),
      source.address = sink.address ∧ path.head? = some source ∧ path.getLast? = some sink ∧
      (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
      (path.zip path.tail).Perm (trace.memorySteps.filter fun edge => edge.1.address = sink.address) := by
  have keys := boundary_keys MemoryToken.address (memory_steps_matched accepted) memory_steps_address
  have terminalUnique := keys.nodup_iff.mp unique
  obtain ⟨source, present, address⟩ := List.mem_map.mp
    (keys.mem_iff.mpr (List.mem_map.mpr ⟨sink, member, rfl⟩))
  obtain ⟨path, head, ⟨last, lastMember, final, same⟩, ordered, permutation⟩ :=
    native_memory_paths hp inverse accepted boundary unique source present
  have equal := List.inj_on_of_nodup_map terminalUnique lastMember member (same.trans address)
  subst last
  exact ⟨source, present, path, address, head, final, ordered, address ▸ permutation⟩

/-- The final native token is the last write in Clean's complete history.
    This follows from native matching and strict chronology, not a result premise. -/
theorem terminal_latest_value [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup)
    {history : TimestampSortedMemoryAccessList} (bound : MemoryHistory trace history)
    {sink : MemoryToken p} (member : sink ∈ trace.terminalMemory) :
    MemoryAccessList.lastWriteValue history.val history.property sink.address = sink.value := by
  obtain ⟨source, sourceMember, path, address, head, final, ordered, permutation⟩ :=
    terminal_path hp inverse accepted boundary unique member
  let rank := fun token : MemoryToken p => (timeOfPair token.time).value
  have upper : ∀ token ∈ path, rank token ≤ rank sink := by
    intro token present
    have weak := ordered.imp Nat.le_of_lt
    have upper := weak.rel_getLast (List.mem_map.mpr ⟨token, present, rfl⟩)
    have last : (path.map rank).getLast? = some (rank sink) := by
      rw [List.getLast?_map, final]
      rfl
    change rank token ≤ (path.map rank).getLast _ at upper
    rw [List.getLast_of_getLast?_eq_some last] at upper
    exact upper
  have writeUpper : ∀ edge ∈ trace.memorySteps, edge.1.address = sink.address →
      rank edge.2 ≤ rank sink := by
    intro edge present same
    have onPath := permutation.mem_iff.mpr (List.mem_filter.mpr ⟨present, by simpa using same⟩)
    exact upper edge.2 (List.mem_of_mem_tail (List.of_mem_zip onPath).2)
  have tokenPresent := (memory_steps_matched accepted).mem_iff.mpr (List.mem_append_left _ member)
  rcases List.mem_append.mp tokenPresent with initial | native
  · have same := List.inj_on_of_nodup_map unique initial sourceMember address.symm
    subst sink
    have noNative : ∀ edge ∈ trace.memorySteps, edge.1.address ≠ source.address := by
      intro edge present equal
      have onPath := permutation.mem_iff.mpr (List.mem_filter.mpr ⟨present, by simpa using equal⟩)
      have increasing := List.pairwise_map.mp ordered
      have first : rank source ≤ rank edge.1 := by
        have weak := increasing.imp (fun {_ _} h => Nat.le_of_lt h)
        have onPathFirst := (List.of_mem_zip onPath).1
        have bound := weak.rel_head onPathFirst
        simpa only [List.head_of_head?_eq_some head] using bound
      have lastBound := writeUpper edge present equal
      have growth := memory_steps_increase hp inverse accepted boundary edge present
      change rank edge.1 < rank edge.2 at growth
      omega
    let event : MemoryAccess := (source.address, source.address, 0, source.value)
    apply last_write_max history.val history.property
      (event := event) (bound.1.mem_iff.mpr (List.mem_append_left _
        (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)))
    intro other present same
    rcases List.mem_append.mp (bound.1.mem_iff.mp present) with initial | native
    · obtain ⟨token, tokenMember, rfl⟩ := List.mem_map.mp initial
      change token.address = source.address at same
      change token.address ≤ source.address
      exact Nat.le_of_eq same
    · obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp native
      exact False.elim (noNative edge edgeMember same)
  · obtain ⟨edge, edgeMember, written⟩ := List.mem_map.mp native
    let event : MemoryAccess :=
      (trace.memoryEpoch + rank sink, sink.address, edge.1.value, sink.value)
    have present : List.Mem event history.val := by
      apply bound.1.mem_iff.mpr
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨edge, edgeMember, by
        change (trace.memoryEpoch + rank edge.2, edge.1.address, edge.1.value, edge.2.value) = _
        rw [memory_steps_address edge edgeMember, written]⟩
    apply last_write_max history.val history.property present
    intro other otherMember same
    rcases List.mem_append.mp (bound.1.mem_iff.mp otherMember) with initial | native
    · obtain ⟨token, tokenMember, rfl⟩ := List.mem_map.mp initial
      have below := below_epoch tokenMember
      change token.address ≤ trace.memoryEpoch + rank sink
      omega
    · obtain ⟨edge, edgeMember, rfl⟩ := List.mem_map.mp native
      have less := writeUpper edge edgeMember same
      change trace.memoryEpoch + rank edge.2 ≤ trace.memoryEpoch + rank sink
      omega

/-- The realized Sail state reads the exact terminal register/RAM values from
    native matching. No claimed terminal value is assumed to be correct. -/
theorem terminal_sail_reads [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before after : State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) (domain : cells.Nodup)
    {history : TimestampSortedMemoryAccessList} (consistent : MemoryHistory trace history)
    (realized : SailStateMatches cells history after) :
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (memoryWord sink.value) after := by
  intro sink member
  obtain ⟨source, present, _, address, _⟩ := terminal_path hp inverse accepted boundary
    (image_unique image domain) member
  obtain ⟨cell, cellMember, _, _, same⟩ := image_sources image source present
  have code : source.address = cell.addressCode := congrArg MemoryToken.address same
  refine ⟨cell, cellMember, ?_, ?_⟩
  · exact code.symm.trans address
  · have read := realized cell cellMember
    have latest := terminal_latest_value hp inverse accepted boundary
      (image_unique image domain) consistent member
    rw [code.symm.trans address, latest] at read
    exact read

end Airbender.Trace.Proofs
