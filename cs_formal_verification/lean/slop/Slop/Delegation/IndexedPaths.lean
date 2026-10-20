import Slop.Delegation.CallPaths

namespace Airbender.Delegation.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem indexed_path_words {path : List (MemoryToken p)} {source : MemoryToken p}
    (head : path.head? = some source) (schedule : Nat → Word)
    (start : source.word = schedule 0)
    (steps : ∀ i, i + 1 < path.length → ∀ edge ∈ path.zip path.tail,
      edge.1.word = schedule i → edge.2.word = schedule (i + 1)) :
    ∀ (i : Nat) (bound : i < path.length), (path[i]'bound).word = schedule i := by
  intro i
  induction i with
  | zero =>
    intro bound
    have first : path[0]'bound = source := by
      have first : path[0]? = some source := by simpa only [List.head?_eq_getElem?] using head
      simpa [List.getElem?_eq_getElem, bound] using first
    exact (congrArg MemoryToken.word first).trans start
  | succ i ih =>
    intro bound
    have edge : (path[i]'(by omega), path[i + 1]'bound) ∈ path.zip path.tail := by
      apply List.mem_iff_getElem.mpr
      refine ⟨i, by simp; omega, ?_⟩
      simp
    exact steps i bound _ edge (ih (by omega))

end Airbender.Delegation.Proofs
