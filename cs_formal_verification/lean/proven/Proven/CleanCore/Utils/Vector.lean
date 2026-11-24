module
public import Mathlib.Tactic.Linarith
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Init.Data.List.Find
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Enumerative.Composition

/-! # `Vector.mapRange` (Clean `Clean.Utils.Vector`, pinned b41c196): transcribed with proofs. -/

@[expose] public section

namespace Airbender

variable {α β : Type} {n m : ℕ}
open Vector (finRange)
namespace Vector
universe u
def mapRange (n : ℕ) (create : ℕ → α) : Vector α n :=
  match n with
  | 0 => #v[]
  | k + 1 => mapRange k create |>.push (create k)

theorem mapRange_succ {n} {create : ℕ → α} :
    mapRange (n + 1) create = (mapRange n create).push (create n) := rfl

theorem getElem_mapRange {n} {create : ℕ → α} :
    ∀ (i : ℕ) (hi : i < n), (mapRange n create)[i] = create i := by
  intros i hi
  induction n
  case zero => simp at hi
  case succ n ih =>
    rw [mapRange_succ]
    by_cases hi' : i < n
    · rw [_root_.Vector.getElem_push_lt hi', ih hi']
    · have i_eq : n = i := by linarith
      subst i_eq
      rw [_root_.Vector.getElem_push_eq]

end Vector

end Airbender
