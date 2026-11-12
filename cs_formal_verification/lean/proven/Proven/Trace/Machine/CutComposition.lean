module
public import Proven.Trace.RVHistory
public import Proven.ISA.RV.Run

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- A cut state contains all memory effects through the given native clock. -/
def CutState (cells : List Cell) (events : List MemoryAccess) (initial : RV.State)
    (clock : Nat) (state : RV.State) : Prop :=
  RVHistory cells (events.filter fun event => decide (event.1 ≤ clock)) initial state

/-- A shared history fixes the state at each cut. -/
theorem cut_state_unique {cells : List Cell} {events : List MemoryAccess} {initial first last : RV.State}
    {clock : Nat} (one : CutState cells events initial clock first)
    (two : CutState cells events initial clock last) : first = last :=
  Trace.Proofs.RVWriteHistory.unique one.writes two.writes

/-- Local RV steps between adjacent memory cuts compose to one run.
    The view supplies each boundary's PC and remaining independent input stream. -/
theorem compose_cuts {Vertex : Type} (clock : Vertex → Nat) (view : Vertex → RV.State → RV.State)
    {cells : List Cell} {events : List MemoryAccess} {initial : RV.State}
    {path : List Vertex} {first last : Vertex} {before after : RV.State}
    (head : path.head? = some first) (endPoint : path.getLast? = some last)
    (start : CutState cells events initial (clock first) before)
    (finish : CutState cells events initial (clock last) after)
    (transitions : ∀ edge ∈ path.zip path.tail, ∃ one two,
      CutState cells events initial (clock edge.1) one ∧ CutState cells events initial (clock edge.2) two ∧
      ∃ next, RV.step (view edge.1 one) = some next ∧ RV.Same next (view edge.2 two)) :
    ∃ final, RV.run (path.length - 1) (view first before) = some final ∧ RV.Same final (view last after) := by
  induction path generalizing first before with
  | nil => simp at head
  | cons a rest ih =>
    have same : a = first := by simpa using head
    subst first
    cases rest with
    | nil =>
      have same : a = last := by simpa using endPoint
      subst last
      have same := cut_state_unique start finish
      subst after
      exact ⟨view a before, rfl, RV.Same.refl _⟩
    | cons b rest =>
      obtain ⟨one, two, past, current, next, stepped, agreement⟩ := transitions (a, b) (by simp)
      have same := cut_state_unique start past
      subst one
      obtain ⟨final, run, same⟩ := ih rfl (by simpa using endPoint) current
        (fun edge member => transitions edge (by
          simpa only [List.tail_cons, List.zip_cons_cons, List.mem_cons] using Or.inr member))
      have run : RV.run rest.length (view b two) = some final := by simpa using run
      obtain ⟨actual, actualRun, actualSame⟩ := (RV.run_same rest.length agreement.symm).some_left run
      refine ⟨actual, ?_, actualSame.symm.trans same⟩
      change (RV.step (view a before)).bind (RV.run rest.length) = some actual
      rw [stepped, Option.bind_some]
      exact actualRun

end Airbender.Trace.Machine.Proofs
