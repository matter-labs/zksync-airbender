import Slop.Trace.TransferBounds
import Slop.Trace.TransferSplit

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

structure NativeInputs (data : Data p) (before : State) (cells : List Cell) : Prop
    extends BoundaryInputs data before cells where
  words : ∀ token ∈ data.initial, token.word.Bounded
  clocks : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded

def Inputs.toNativeInputs {data : Data p} {before : State} {cells : List Cell}
    (inputs : Inputs data before cells) : NativeInputs data before cells :=
  ⟨inputs.toBoundaryInputs, image_bounds inputs.initialization, image_clocks inputs.initialization⟩

theorem native_cell_source {data : Data p} {before : State} {cells : List Cell}
    (inputs : NativeInputs data before cells) {cell : Cell} (member : cell ∈ cells) :
    ∃ token ∈ data.initial, token.address = cell.addressCode ∧
      cell.read before = .ok token.word.toBitVec before ∧
      token.word = Word.ofBitVec token.word.toBitVec := by
  obtain ⟨token, present, same⟩ := List.mem_map.mp
    (inputs.addresses.mem_iff.mpr (List.mem_map.mpr ⟨cell, member, rfl⟩))
  obtain ⟨actual, _, address, read⟩ := inputs.reads token present
  have equal : actual = cell := cell_address_injective (address.trans same)
  subst actual
  have bound := inputs.words token present
  refine ⟨token, present, same, read, ?_⟩
  apply Word.eq_of_value bound (Word.ofBitVec_bound _)
  rw [Word.ofBitVec_value, Word.toBitVec_toNat bound]

theorem native_produced_bounds {data : Data p} (inputs : NativeInputs data before cells)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded) :
    ∀ token ∈ data.initial ++ data.steps.map Prod.snd, (timeOfPair token.time).Bounded := by
  intro token member
  rcases List.mem_append.mp member with initial | written
  · exact inputs.clocks token initial
  · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
    exact writes edge present

theorem split_native_sail_state {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : NativeInputs data before cells)
    (rules : WriteRules data)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) (cutoff : Nat) :
    ∃ (middle : List (MemoryToken p)) (events : List MemoryAccess) (atCut : State),
      Facts ⟨data.initial, middle, beforeSteps data cutoff⟩ ∧
      Facts ⟨middle, data.terminal, afterSteps data cutoff⟩ ∧
      events.Perm ((beforeSteps data cutoff).map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ SailHistory cells events before atCut ∧
      NativeInputs ⟨middle, data.terminal, afterSteps data cutoff⟩ atCut cells := by
  obtain ⟨middle, earlier, later⟩ := split_at facts cutoff
  have initialized : BoundaryInputs ⟨data.initial, middle, beforeSteps data cutoff⟩ before cells :=
    ⟨inputs.addresses, inputs.distinct, inputs.reads⟩
  obtain ⟨history, events, atCut, matching, native, ordered, actual, final⟩ :=
    native_sail_history_at_boundary earlier initialized aligned
      (fun edge member => zero edge (List.mem_of_mem_filter member))
  have reads := terminal_sail_reads_at_boundary earlier initialized matching final
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have produced (token : MemoryToken p) (member : token ∈ middle) :
      token ∈ data.initial ++ data.steps.map Prod.snd := by
    have prefixMember := earlier.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member))
    rcases List.mem_append.mp prefixMember with initial | written
    · exact List.mem_append.mpr (Or.inl initial)
    · obtain ⟨edge, present, rfl⟩ := List.mem_map.mp written
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
        ⟨edge, List.mem_of_mem_filter present, rfl⟩))
  exact ⟨middle, events, atCut, earlier, later, native, ordered, actual,
    ⟨⟨keys.symm.trans inputs.addresses, inputs.distinct, reads⟩,
      fun token member => produced_bounds_of_seed facts inputs.words rules token (produced token member),
      fun token member => native_produced_bounds inputs writes token (produced token member)⟩⟩

def windowSteps (data : Data p) (lower upper : Nat) :=
  beforeSteps ⟨data.initial, data.terminal, afterSteps data lower⟩ upper

theorem split_native_sail_window_at_boundary {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : NativeInputs data before cells)
    (rules : WriteRules data)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) (lower upper : Nat) :
    ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
      (atStart atFinish : State),
      Facts ⟨data.initial, start, beforeSteps data lower⟩ ∧
      Facts ⟨start, finish, windowSteps data lower upper⟩ ∧
      earlierEvents.Perm ((beforeSteps data lower).map transferEvent) ∧
      spanEvents.Perm ((windowSteps data lower upper).map transferEvent) ∧
      SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
      NativeInputs ⟨start, finish, windowSteps data lower upper⟩ atStart cells ∧
      NativeInputs ⟨finish, data.terminal,
        afterSteps ⟨start, data.terminal, afterSteps data lower⟩ upper⟩ atFinish cells := by
  obtain ⟨start, earlierEvents, atStart, earlier, later, firstPerm, _, firstHistory, startInputs⟩ :=
    split_native_sail_state facts inputs rules writes aligned zero lower
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
    split_native_sail_state later startInputs suffixRules
      (fun edge member => writes edge (List.mem_of_mem_filter member)) aligned
      (fun edge member => zero edge (List.mem_of_mem_filter member)) upper
  exact ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, earlier, spanFacts,
    firstPerm, secondPerm, firstHistory, secondHistory,
    ⟨⟨startInputs.addresses, startInputs.distinct, startInputs.reads⟩,
      startInputs.words, startInputs.clocks⟩, finishInputs⟩

theorem split_native_sail_window {data : Data p} (facts : Facts data)
    {before : State} {cells : List Cell} (inputs : Inputs data before cells)
    (rules : WriteRules data)
    (writes : ∀ edge ∈ data.steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0) (lower upper : Nat) :
    ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
      (atStart atFinish : State),
      Facts ⟨data.initial, start, beforeSteps data lower⟩ ∧
      Facts ⟨start, finish, windowSteps data lower upper⟩ ∧
      earlierEvents.Perm ((beforeSteps data lower).map transferEvent) ∧
      spanEvents.Perm ((windowSteps data lower upper).map transferEvent) ∧
      SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
      NativeInputs ⟨start, finish, windowSteps data lower upper⟩ atStart cells ∧
      NativeInputs ⟨finish, data.terminal,
        afterSteps ⟨start, data.terminal, afterSteps data lower⟩ upper⟩ atFinish cells :=
  split_native_sail_window_at_boundary facts inputs.toNativeInputs rules writes aligned zero lower upper

end Airbender.Trace.Proofs.Transfer
