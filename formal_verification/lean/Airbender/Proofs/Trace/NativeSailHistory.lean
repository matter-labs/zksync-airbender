import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Trace.SailHistory
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.Addresses

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]
open Reference.RiscV.Sail

theorem split_history (events : List MemoryAccess)
    (sorted : MemoryAccessList.isTimestampSorted events) (cut : Nat) :
    List.append (α := MemoryAccess) (events.filter fun event => decide (cut ≤ event.1))
      (events.filter fun event => decide (event.1 < cut)) = events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have tail := List.pairwise_cons.mp sorted
    by_cases recent : cut ≤ event.1
    · simp only [List.filter_cons, recent,
        Nat.not_lt.mpr recent, decide_false]
      exact congrArg (List.cons event) (ih tail.2)
    · have allOld : ∀ next ∈ rest, next.1 < cut := by
        intro next member
        have less := tail.1 next member
        change next.1 < event.1 at less
        omega
      have noRecent : (rest.filter fun next => decide (cut ≤ next.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro next member
        simp only [decide_eq_true_eq]
        exact Nat.not_le.mpr (allOld next member)
      have oldTail : (rest.filter fun next => decide (next.1 < cut)) = rest := by
        apply List.filter_eq_self.mpr
        intro next member
        simpa only [decide_eq_true_eq] using allOld next member
      simp [recent, Nat.lt_of_not_ge recent, noRecent, oldTail]

theorem split_memory_history (initial native : List MemoryAccess) (cut : Nat)
    (initializedLow : ∀ event ∈ initial, event.1 < cut)
    (nativeHigh : ∀ event ∈ native, cut ≤ event.1)
    {history : TimestampSortedMemoryAccessList}
    (permutation : history.val.Perm (List.append (α := MemoryAccess) initial native)) :
    ∃ (events : List MemoryAccess) (seed : TimestampSortedMemoryAccessList),
      List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm native ∧ seed.val.Perm initial := by
  let recent := fun event : MemoryAccess => decide (cut ≤ event.1)
  let old := fun event : MemoryAccess => decide (event.1 < cut)
  have emptyInitial : (initial).filter recent = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member
    simpa only [recent, decide_eq_true_eq] using Nat.not_le.mpr (initializedLow event member)
  have fullInitial : (initial).filter old =
      initial := by
    apply List.filter_eq_self.mpr
    intro event member
    simpa only [old, decide_eq_true_eq] using initializedLow event member
  have fullNative : native.filter recent = native := by
    apply List.filter_eq_self.mpr
    intro event member
    simpa only [recent, decide_eq_true_eq] using nativeHigh event member
  have emptyNative : native.filter old = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro event member
    simpa only [old, decide_eq_true_eq] using Nat.not_lt.mpr (nativeHigh event member)
  let seed : TimestampSortedMemoryAccessList :=
    ⟨history.val.filter old, history.property.filter _⟩
  have recentEvents : (List.append (α := MemoryAccess) initial native).filter recent = native := by
    calc
      _ = List.append (α := MemoryAccess)
          ((initial).filter recent)
          (native.filter recent) := by
        simp only [List.append_eq, List.filter_append]
      _ = List.append (α := MemoryAccess) [] native :=
        congrArg₂ (List.append (α := MemoryAccess)) emptyInitial fullNative
      _ = _ := rfl
  have initialEvents : (List.append (α := MemoryAccess) initial native).filter old = initial := by
    calc
      _ = List.append (α := MemoryAccess)
          ((initial).filter old)
          (native.filter old) := by
        simp only [List.append_eq, List.filter_append]
      _ = List.append (α := MemoryAccess)
          (initial) [] :=
        congrArg₂ (List.append (α := MemoryAccess)) fullInitial emptyNative
      _ = _ := List.append_nil _
  refine ⟨history.val.filter recent, seed,
    split_history _ history.property cut, ?_, ?_⟩
  · exact recentEvents ▸ permutation.filter recent
  · exact initialEvents ▸ permutation.filter old

/-- Separate the checked global history at its initialization epoch. This
    retains every native event exactly once and the actual public seed values. -/
theorem native_history_parts [Fact p.Prime] {trace : Data p Kind}
    {history : TimestampSortedMemoryAccessList} (bound : MemoryHistory trace history) :
    ∃ (events : List MemoryAccess) (seed : TimestampSortedMemoryAccessList),
      List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧
      seed.val.Perm (trace.initialMemory.map fun token =>
        (token.address, token.address, 0, token.value)) := by
  apply split_memory_history _ _ trace.memoryEpoch ?_ ?_ bound.1
  · intro event member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact below_epoch present
  · intro event member
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
    exact Nat.le_add_right _ _

theorem native_event_cells [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : State} {cells : List Cell} (image : initialImage before cells = some trace.initialMemory) :
    ∀ event ∈ trace.nativeEvents, ∃ cell ∈ cells, cell.addressCode = event.2.1 := by
  intro event member
  change event ∈ trace.memorySteps.map (fun edge =>
    (trace.memoryEpoch + (timeOfPair edge.2.time).value, edge.1.address, edge.1.value, edge.2.value)) at member
  obtain ⟨edge, edgeMember, equal⟩ := List.mem_map.mp member
  subst event
  change edge ∈ trace.rows.flatMap Row.memorySteps at edgeMember
  obtain ⟨row, rowMember, rowEdge⟩ := List.mem_flatMap.mp edgeMember
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp rowEdge
  obtain ⟨cell, present, address⟩ := initialized_cells hp inverse accepted boundary image row rowMember
    port (by simpa using portMember)
  exact ⟨cell, present, address.symm⟩

/-- Realize exactly the accepted native transfers. The remaining x0 condition
    is internal: it must be discharged using the bound decoder before publishing
    restricted-ISA trace soundness. No read-value or result premise is introduced. -/
theorem native_sail_history [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : State} {cells : List Cell} (image : initialImage before cells = some trace.initialMemory)
    (domain : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ event ∈ trace.nativeEvents, event.2.1 = (Cell.register 0).addressCode →
      memoryWord event.2.2.2 = 0) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (seed : TimestampSortedMemoryAccessList) (after : State),
      MemoryHistory trace history ∧ List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧ SailHistory cells events before after ∧
      SailStateMatches cells history after := by
  obtain ⟨history, checked⟩ := native_memory_history hp inverse accepted boundary (image_unique image domain)
  obtain ⟨events, seed, combined, permutation, initial⟩ := native_history_parts checked
  have ordered : MemoryAccessList.isTimestampSorted (List.append (α := MemoryAccess) events seed.val) := by
    simpa only [combined] using history.property
  have consistent : MemoryAccessList.isConsistentOnline
      (List.append (α := MemoryAccess) events seed.val) ordered := by
    simpa only [combined] using checked.2
  obtain ⟨after, actual, final⟩ := realize_history events seed
    (initial_history_matches image domain seed initial) aligned
    (fun event member => native_event_cells hp inverse accepted boundary image event
      (permutation.mem_iff.mp member))
    (fun event member => zero event (permutation.mem_iff.mp member)) ordered consistent
  refine ⟨history, events, seed, after, checked, combined, permutation, actual, ?_⟩
  intro cell member
  simpa only [combined] using final cell member

end Airbender.Trace.Proofs
