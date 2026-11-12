module
public import Proven.Trace.RVTransfer
public import Proven.Trace.TransferBoundary

@[expose] public section

/-! RV twins of `TransferBoundary.split_native_sail_state` / `split_native_sail_window_at_boundary`: a native
    history cut at native-clock times into RV histories (`RVHistory`) between actual `RV.State`s, each cut state
    reading the cut's tokens. RAM cells are RAM at any address, the shadow RAM below `ROM_END` included. -/

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

/-- RV sibling of `NativeInputs`: an RV boundary with canonical seed words and bounded seed clocks. -/
structure RVNativeInputs (data : Data p) (before : RV.State) (cells : List Cell) : Prop
    extends RVBoundaryInputs data before cells where
  words : ∀ token ∈ data.initial, token.word.Bounded
  clocks : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded

theorem rv_split_native_state {data : Data p} (facts : Facts data)
    {before : RV.State} {cells : List Cell} (inputs : RVNativeInputs data before cells)
    (rules : WriteRules data)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) (cutoff : Nat) :
    ∃ (middle : List (MemoryToken p)) (events : List MemoryAccess) (atCut : RV.State),
      Facts ⟨data.initial, middle, beforeSteps data cutoff⟩ ∧
      Facts ⟨middle, data.terminal, afterSteps data cutoff⟩ ∧
      events.Perm ((beforeSteps data cutoff).map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ RVHistory cells events before atCut ∧
      RVNativeInputs ⟨middle, data.terminal, afterSteps data cutoff⟩ atCut cells := by
  obtain ⟨middle, earlier, later⟩ := split_at facts cutoff
  have initialized : RVBoundaryInputs ⟨data.initial, middle, beforeSteps data cutoff⟩ before cells :=
    ⟨⟨inputs.addresses, inputs.distinct⟩, inputs.reads⟩
  obtain ⟨history, events, atCut, matching, native, ordered, actual, final⟩ :=
    rv_native_history_at_boundary earlier initialized aligned
      (fun edge member => zero edge (List.mem_of_mem_filter member))
  have reads := rv_terminal_reads_at_boundary earlier initialized matching final
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have produced (token : MemoryToken p) (member : token ∈ middle) :
      token ∈ data.initial ++ data.steps.map Prod.snd := by
    have prefixMember := earlier.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member))
    rcases List.mem_append.mp prefixMember with initial | written
    · exact List.mem_append.mpr (Or.inl initial)
    · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
        ⟨edge, List.mem_of_mem_filter present, rfl⟩))
  have producedClocks : ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
    intro token member
    rcases List.mem_append.mp member with initial | written
    · exact inputs.clocks token initial
    · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
      exact writes edge present
  exact ⟨middle, events, atCut, earlier, later, native, ordered, actual,
    ⟨⟨⟨keys.symm.trans inputs.addresses, inputs.distinct⟩, reads⟩,
      fun token member => produced_bounds_of_seed facts inputs.words rules token (produced token member),
      fun token member => producedClocks token (produced token member)⟩⟩

theorem rv_split_native_window_at_boundary {data : Data p} (facts : Facts data)
    {before : RV.State} {cells : List Cell} (inputs : RVNativeInputs data before cells)
    (rules : WriteRules data)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) (lower upper : Nat) :
    ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
      (atStart atFinish : RV.State),
      Facts ⟨data.initial, start, beforeSteps data lower⟩ ∧
      Facts ⟨start, finish, windowSteps data lower upper⟩ ∧
      earlierEvents.Perm ((beforeSteps data lower).map transferEvent) ∧
      spanEvents.Perm ((windowSteps data lower upper).map transferEvent) ∧
      RVHistory cells earlierEvents before atStart ∧ RVHistory cells spanEvents atStart atFinish ∧
      RVNativeInputs ⟨start, finish, windowSteps data lower upper⟩ atStart cells ∧
      RVNativeInputs ⟨finish, data.terminal,
        afterSteps ⟨start, data.terminal, afterSteps data lower⟩ upper⟩ atFinish cells := by
  obtain ⟨start, earlierEvents, atStart, earlier, later, firstPerm, _, firstHistory, startInputs⟩ :=
    rv_split_native_state facts inputs rules writes aligned zero lower
  have suffixRules : WriteRules ⟨start, data.terminal, afterSteps data lower⟩ := by
    intro edge member reads
    apply rules edge (List.mem_of_mem_filter member)
    intro previous present beforeEdge
    by_cases inSuffix : previous ∈ afterSteps data lower
    · exact reads previous inSuffix beforeEdge
    · have originalBounds := produced_bounds_of_seed facts inputs.words rules
      exact originalBounds previous.1 (facts.matching.mem_iff.mpr
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨previous, present, rfl⟩))))
  obtain ⟨finish, spanEvents, atFinish, spanFacts, _, secondPerm, _, secondHistory, finishInputs⟩ :=
    rv_split_native_state later startInputs suffixRules
      (fun edge member => writes edge (List.mem_of_mem_filter member)) aligned
      (fun edge member => zero edge (List.mem_of_mem_filter member)) upper
  exact ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, earlier, spanFacts,
    firstPerm, secondPerm, firstHistory, secondHistory,
    ⟨⟨⟨startInputs.addresses, startInputs.distinct⟩, startInputs.reads⟩,
      startInputs.words, startInputs.clocks⟩, finishInputs⟩

end Airbender.Trace.Proofs.Transfer
