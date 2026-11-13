module
public import Proven.Trace.SeedTransfer
public import Proven.Trace.RVHistory

@[expose] public section

/-! RV twins of the state-touching `Transfer` lemmas (`TransferHistory.native_sail_history_at_boundary`,
    `TransferTerminal.terminal_sail_reads_at_boundary`): the seeds are read from an `RV.State` (`Cell.readRV`) and
    the history is an `RVHistory` (`Cell.applyRV`). The address-domain reasoning is the state-free `SeedTransfer`. -/

namespace Airbender.Trace.Proofs.Transfer
set_option warningAsError true
set_option maxRecDepth 16384

/-- RV sibling of `BoundaryInputs`: the public seed domain, each seed token read from the starting RV state. -/
structure RVBoundaryInputs (data : Data p) (before : RV.State) (cells : List Cell) : Prop
    extends SeedTransfer.SeedInputs data cells where
  reads : ∀ token ∈ data.initial, ∃ cell ∈ cells, cell.addressCode = token.address ∧
    cell.readRV before = some (memoryWord token.value)

theorem rv_boundary_history_matches {data : Data p} {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) (seed : TimestampSortedMemoryAccessList)
    (permutation : seed.val.Perm
      (data.initial.map fun token => (token.address, token.address, 0, token.value))) :
    RVStateMatches cells seed before := by
  apply rv_seed_history_matches (inputs.addresses.nodup_iff.mpr inputs.distinct) ?_ seed permutation
  intro cell member
  obtain ⟨token, present, address⟩ := List.mem_map.mp (inputs.addresses.mem_iff.mpr
    (List.mem_map.mpr ⟨cell, member, rfl⟩))
  obtain ⟨actual, _, equal, read⟩ := inputs.reads token present
  have same : actual = cell := cell_address_injective (equal.trans address)
  subst actual
  exact ⟨token, present, address, read⟩

theorem rv_native_history_at_boundary {data : Data p} (facts : Facts data)
    {before : RV.State} {cells : List Cell} (inputs : RVBoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : RV.State),
      history.val.Perm (labeledEvents data) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      RVHistory cells events before after ∧ RVStateMatches cells history after := by
  obtain ⟨history, permutation, consistent⟩ := SeedTransfer.labeled_history facts inputs.toSeedInputs
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
      Nat.one_ne_zero, and_false, ite_false]
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
    exact SeedTransfer.initialized_cell facts inputs.toSeedInputs present
  have zeroEvents (event : MemoryAccess) (member : event ∈ events)
      (same : event.2.1 = (Cell.register 0).addressCode) : memoryWord event.2.2.2 = 0 := by
    obtain ⟨edge, present, rfl⟩ := source event member
    exact zero edge present same
  obtain ⟨after, actual, final⟩ := rv_realize_history events seed
    (rv_boundary_history_matches inputs seed initialized) aligned addresses zeroEvents ordered online
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
    rv_history_relabel (nativeEventClock data) actual, ?_⟩
  intro cell member
  simpa only [combined] using final cell member

theorem rv_terminal_reads_at_boundary {data : Data p} (facts : Facts data)
    {before after : RV.State} {cells : List Cell} (inputs : RVBoundaryInputs data before cells)
    {history : TimestampSortedMemoryAccessList} (bound : history.val.Perm (labeledEvents data))
    (realized : RVStateMatches cells history after) :
    ∀ sink ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV after = some (memoryWord sink.value) := by
  intro sink member
  obtain ⟨source, present, address, _⟩ := SeedTransfer.terminal_path facts inputs.toSeedInputs member
  obtain ⟨cell, cellMember, code, _⟩ := inputs.reads source present
  refine ⟨cell, cellMember, code.trans address, ?_⟩
  have read := realized cell cellMember
  have latest := SeedTransfer.terminal_latest_value facts inputs.toSeedInputs bound member
  rw [code.trans address, latest] at read
  exact read

end Airbender.Trace.Proofs.Transfer
