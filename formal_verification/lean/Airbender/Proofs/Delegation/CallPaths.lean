import Airbender.Proofs.Delegation.Readonly

namespace Airbender.Delegation.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem path_word_sequence {path : List (MemoryToken p)} {source : MemoryToken p}
    (head : path.head? = some source) (advance : Word → Word)
    (steps : ∀ edge ∈ path.zip path.tail, edge.2.word = advance edge.1.word) :
    ∀ (n : Nat) (bound : n < path.length), (path[n]'bound).word = advance^[n] source.word := by
  intro n
  induction n with
  | zero =>
    intro bound
    have first : path[0]'bound = source := by
      have first : path[0]? = some source := by simpa only [List.head?_eq_getElem?] using head
      simpa [List.getElem?_eq_getElem, bound] using first
    simp only [first, Function.iterate_zero, id_eq]
  | succ n ih =>
    intro bound
    have edge : (path[n]'(by omega), path[n + 1]'bound) ∈ path.zip path.tail := by
      apply List.mem_iff_getElem.mpr
      refine ⟨n, by simp; omega, ?_⟩
      simp
    rw [steps _ edge, ih (by omega), Function.iterate_succ_apply']

theorem rows_from_path {path : List (MemoryToken p)} {rows : List α}
    (edge : α → MemoryToken p × MemoryToken p)
    (matching : (path.zip path.tail).Perm (rows.map edge)) :
    ∃ ordered : List α, ordered.Perm rows ∧ path.zip path.tail = ordered.map edge := by
  have lifted : ∃ ordered : List α, path.zip path.tail = ordered.map edge ∧ ordered.Perm rows := by
    have same := congrFun (congrFun (List.eq_map_comp_perm edge) (path.zip path.tail)) rows
    exact same.mpr matching
  obtain ⟨ordered, same, perm⟩ := lifted
  exact ⟨ordered, perm, same⟩

end Airbender.Delegation.Proofs
