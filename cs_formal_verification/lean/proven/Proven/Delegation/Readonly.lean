module
public import Human.Helpers.Memory.Values
public import Proven.KernelRfl
public import Proven.OpIndex
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem path_word_constant {path : List (MemoryToken p)} {source : MemoryToken p}
    (head : path.head? = some source)
    (copies : ∀ edge ∈ path.zip path.tail, edge.1.word = edge.2.word) :
    ∀ token ∈ path, token.word = source.word := by
  induction path generalizing source with
  | nil => simp at head
  | cons first rest ih =>
    have same : first = source := by simpa using head
    subst source
    intro token member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · cases rest with
      | nil => simp at member
      | cons second tail =>
        have next := copies (first, second) (by simp)
        have result := ih (by rfl : (second :: tail).head? = some second)
          (fun edge member => copies edge (List.mem_cons_of_mem _ member)) token member
        exact result.trans next.symm

end Airbender.Delegation.Proofs
