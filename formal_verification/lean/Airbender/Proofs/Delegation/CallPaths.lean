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

theorem ordered_rows_from_path {path : List (MemoryToken p)} {rows : List α}
    (edge : α → MemoryToken p × MemoryToken p)
    (matching : (path.zip path.tail).Perm (rows.map edge))
    (increasing : (path.map fun token => (timeOfPair token.time).value).Pairwise (· < ·)) :
    ∃ ordered : List α, ordered.Perm rows ∧ path.zip path.tail = ordered.map edge ∧
      ordered.Pairwise (fun a b => (timeOfPair (edge a).2.time).value < (timeOfPair (edge b).2.time).value) := by
  obtain ⟨ordered, perm, edges⟩ := rows_from_path edge matching
  have projected : (path.zip path.tail).map Prod.snd = path.tail := by
    rw [List.map_snd_zip]
    simp
  have times : ordered.map (fun row => (timeOfPair (edge row).2.time).value) =
      path.tail.map (fun token => (timeOfPair token.time).value) := by
    have second := congrArg (List.map fun pair => (timeOfPair pair.2.time).value) edges
    calc
      ordered.map (fun row => (timeOfPair (edge row).2.time).value) =
          (path.zip path.tail).map (fun pair => (timeOfPair pair.2.time).value) := by
        simpa only [List.map_map, Function.comp_def] using second.symm
      _ = path.tail.map (fun token => (timeOfPair token.time).value) := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map fun token => (timeOfPair token.time).value) projected
  refine ⟨ordered, perm, edges, ?_⟩
  rw [← List.pairwise_map, times]
  simpa only [List.map_tail] using increasing.tail

end Airbender.Delegation.Proofs
