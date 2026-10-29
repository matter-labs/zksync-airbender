import Airbender.Proofs.Trace.CycleComposition

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Compose native memory cuts while carrying an external-stream position. -/
theorem compose_rebased_cuts_with_count
    {step : State × Nat → State × Nat → Prop}
    {cells : List Cell} {events : List MemoryAccess} {initial : State}
    {path : List ((Nat × BitVec 32) × Nat)}
    {first last : (Nat × BitVec 32) × Nat} {before after : State}
    (head : path.head? = some first) (endPoint : path.getLast? = some last)
    (start : CutState cells events initial first.1.1 before)
    (finish : CutState cells events initial last.1.1 after)
    (transitions : ∀ edge ∈ path.zip path.tail, ∃ one two,
      CutState cells events initial edge.1.1.1 one ∧
      CutState cells events initial edge.2.1.1 two ∧
      step (retiredState one edge.1.1.2, edge.1.2)
        (retiredState two edge.2.1.2, edge.2.2)) :
    Relation.ReflTransGen step (retiredState before first.1.2, first.2)
      (retiredState after last.1.2, last.2) := by
  induction path generalizing first before with
  | nil => simp at head
  | cons a rest ih =>
    have same : a = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : a = last := by simpa using endPoint
      subst last
      have same := sail_history_deterministic start finish
      subst after
      exact .refl
    | cons b rest =>
      obtain ⟨one, two, past, current, transition⟩ := transitions (a, b) (by simp)
      have same := sail_history_deterministic start past
      subst one
      exact (Relation.ReflTransGen.single transition).trans
        (ih rfl (by simpa using endPoint) current (fun edge member => transitions edge
          (by simpa only [List.tail_cons, List.zip_cons_cons, List.mem_cons] using Or.inr member)))

/-- The first indexed cycle starts at the original public Sail state. -/
theorem compose_cuts_with_count {step : State × Nat → State × Nat → Prop}
    {cells : List Cell} {events : List MemoryAccess} {initial after : State}
    {path : List ((Nat × BitVec 32) × Nat)} {first last : (Nat × BitVec 32) × Nat}
    (head : path.head? = some first) (endPoint : path.getLast? = some last)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok first.1.2 initial)
    (start : CutState cells events initial first.1.1 initial)
    (finish : CutState cells events initial last.1.1 after)
    (transitions : ∀ edge ∈ path.zip path.tail, ∃ one two,
      CutState cells events initial edge.1.1.1 one ∧
      CutState cells events initial edge.2.1.1 two ∧
      step (retiredState one edge.1.1.2, edge.1.2)
        (retiredState two edge.2.1.2, edge.2.2) ∧
      (run (SailRV32.Functions.get_arch_pc ()) one = .ok edge.1.1.2 one →
        step (one, edge.1.2) (retiredState two edge.2.1.2, edge.2.2))) :
    ∃ finalState, Relation.ReflTransGen step (initial, first.2) (finalState, last.2) ∧
      (finalState = after ∧ first = last ∨ finalState = retiredState after last.1.2) := by
  cases path with
  | nil => simp at head
  | cons a rest =>
    have same : a = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : a = last := by simpa using endPoint
      subst last
      have same := sail_history_deterministic start finish
      exact ⟨initial, .refl, Or.inl ⟨same, rfl⟩⟩
    | cons b rest =>
      obtain ⟨one, two, past, current, _, transition⟩ := transitions (a, b) (by simp)
      have same := sail_history_deterministic start past
      subst one
      refine ⟨retiredState after last.1.2,
        (Relation.ReflTransGen.single (transition pc)).trans ?_, Or.inr rfl⟩
      exact compose_rebased_cuts_with_count rfl (by simpa using endPoint) current finish
        (fun edge member => by
          obtain ⟨one, two, past, current, transition, _⟩ := transitions edge
            (by simpa only [List.tail_cons, List.zip_cons_cons, List.mem_cons] using Or.inr member)
          exact ⟨one, two, past, current, transition⟩)

end Airbender.Trace.Proofs
