import Airbender.Proofs.Trace.TransferHistory
import Airbender.Proofs.Trace.Terminal

namespace Airbender.Trace.Proofs.Transfer
open Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem raw_time_injective {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : Inputs data before cells)
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

theorem event_clock_le {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : Inputs data before cells)
    {first last : MemoryAccess} (firstMember : first ∈ rawEvents data)
    (lastMember : last ∈ rawEvents data) (address : first.2.1 = last.2.1)
    (time : last.1 ≤ first.1) : eventClock data last ≤ eventClock data first := by
  rcases Nat.lt_or_eq_of_le time with earlier | same
  · exact Nat.le_of_lt (event_clock_order data (raw_seed_bound lastMember) earlier)
  · rw [raw_time_injective facts inputs firstMember lastMember address same.symm]

theorem terminal_path {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : Inputs data before cells)
    {sink : MemoryToken p} (member : sink ∈ data.terminal) :
    ∃ source ∈ data.initial, source.address = sink.address ∧
      ∃ path : List (MemoryToken p), path.head? = some source ∧ path.getLast? = some sink ∧
        (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·) ∧
        (path.zip path.tail).Perm (data.steps.filter fun edge => edge.1.address = sink.address) := by
  have unique : (data.initial.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
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

theorem terminal_latest_value {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : Inputs data before cells)
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
      rw [image_addresses inputs.initialization]
      exact inputs.distinct
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

theorem terminal_sail_reads {data : Data p} (facts : Facts data)
    {before after : State} {cells : List Cell} (inputs : Inputs data before cells)
    {history : TimestampSortedMemoryAccessList} (bound : history.val.Perm (labeledEvents data))
    (realized : SailStateMatches cells history after) :
    ∀ sink ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (memoryWord sink.value) after := by
  intro sink member
  obtain ⟨source, present, address, _⟩ := terminal_path facts inputs member
  obtain ⟨cell, cellMember, _, _, same⟩ := image_sources inputs.initialization source present
  have code : source.address = cell.addressCode := congrArg MemoryToken.address same
  refine ⟨cell, cellMember, code.symm.trans address, ?_⟩
  have read := realized cell cellMember
  have latest := terminal_latest_value facts inputs bound member
  rw [code.symm.trans address, latest] at read
  exact read

end Airbender.Trace.Proofs.Transfer
