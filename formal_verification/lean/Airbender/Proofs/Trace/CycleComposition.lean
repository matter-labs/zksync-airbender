import Airbender.Proofs.Trace.HistoryWindow
import Airbender.Proofs.Trace.CompositionCore

namespace Airbender.Trace.Proofs
open Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384

/-- A fixed sequence of actual Sail cell writes determines the entire state. -/
theorem sail_history_deterministic {cells : List Cell} {events : List MemoryAccess}
    {before first second : State} (one : SailHistory cells events before first)
    (two : SailHistory cells events before second) : first = second := by
  induction one generalizing second with
  | nil => cases two; rfl
  | @cons event rest before middle first past cell member address read written ih =>
    cases two with
    | cons previous other included code old write =>
      have same := ih previous
      subst same
      have sameCell := cell_address_injective (address.trans code.symm)
      subst other
      exact (EStateM.Result.ok.inj (written.symm.trans write)).2

/-- Actual writes through the upper cut are precisely the current cycle and its
    prefix. No ordering of simultaneous writes is supplied independently. -/
theorem history_prefix_of_window {cells : List Cell} {events : List MemoryAccess}
    {initial before after : State} {low high : Nat}
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (bounds : low ≤ high)
    (past : SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) initial before)
    (current : SailHistory cells (events.filter fun event => decide (low < event.1 ∧ event.1 ≤ high)) before after) :
    SailHistory cells (events.filter fun event => decide (event.1 ≤ high)) initial after := by
  have split := Delegation.Proofs.split_clock (events.filter fun event => decide (event.1 ≤ high))
    (ordered.sublist List.filter_sublist) (low + 1)
  have newer : ((events.filter fun event => decide (event.1 ≤ high)).filter
      fun event => decide (low + 1 ≤ event.1)) =
      events.filter (fun event => decide (low < event.1 ∧ event.1 ≤ high)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have older : ((events.filter fun event => decide (event.1 ≤ high)).filter
      fun event => decide (event.1 < low + 1)) =
      events.filter (fun event => decide (event.1 ≤ low)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro event _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [newer, older] at split
  rw [← split]
  exact sail_history_append.mpr ⟨before, past, current⟩

def CutState (cells : List Cell) (events : List MemoryAccess) (initial : State)
    (clock : Nat) (state : State) : Prop :=
  SailHistory cells (events.filter fun event => decide (event.1 ≤ clock)) initial state

theorem compose_rebased_cuts {step : State → State → Prop}
    {cells : List Cell} {events : List MemoryAccess} {initial : State}
    {path : List (Nat × BitVec 32)} {first last : Nat × BitVec 32} {before after : State}
    (head : path.head? = some first) (endPoint : path.getLast? = some last)
    (start : CutState cells events initial first.1 before)
    (finish : CutState cells events initial last.1 after)
    (transitions : ∀ edge ∈ path.zip path.tail, ∃ one two,
      CutState cells events initial edge.1.1 one ∧ CutState cells events initial edge.2.1 two ∧
      step (retiredState one edge.1.2) (retiredState two edge.2.2)) :
    Relation.ReflTransGen step (retiredState before first.2) (retiredState after last.2) := by
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

/-- Complete cut-by-cut execution begins at the original public state. The
    first-step rule handles its unconstrained initial nextPC; all later states
    use the checked retirement view. -/
theorem compose_cuts {step : State → State → Prop}
    {cells : List Cell} {events : List MemoryAccess} {initial after : State}
    {path : List (Nat × BitVec 32)} {first last : Nat × BitVec 32}
    (head : path.head? = some first) (endPoint : path.getLast? = some last)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok first.2 initial)
    (start : CutState cells events initial first.1 initial)
    (finish : CutState cells events initial last.1 after)
    (transitions : ∀ edge ∈ path.zip path.tail, ∃ one two,
      CutState cells events initial edge.1.1 one ∧ CutState cells events initial edge.2.1 two ∧
      step (retiredState one edge.1.2) (retiredState two edge.2.2) ∧
      (run (SailRV32.Functions.get_arch_pc ()) one = .ok edge.1.2 one →
        step one (retiredState two edge.2.2))) :
    ∃ finalState, Relation.ReflTransGen step initial finalState ∧
      (finalState = after ∧ first = last ∨ finalState = retiredState after last.2) := by
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
      refine ⟨retiredState after last.2, (Relation.ReflTransGen.single (transition pc)).trans ?_, Or.inr rfl⟩
      exact compose_rebased_cuts rfl (by simpa using endPoint) current finish
        (fun edge member => by
          obtain ⟨one, two, past, current, transition, _⟩ := transitions edge
            (by simpa only [List.tail_cons, List.zip_cons_cons, List.mem_cons] using Or.inr member)
          exact ⟨one, two, past, current, transition⟩)

end Airbender.Trace.Proofs
