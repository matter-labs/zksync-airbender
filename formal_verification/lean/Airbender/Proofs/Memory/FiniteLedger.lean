import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.FinRange

namespace Airbender.PrefixLedgerProofs
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem compose {α : Type} (a b c w r v s : List α)
    (first : (a ++ w).Perm (b ++ r)) (second : (b ++ v).Perm (c ++ s)) :
    (a ++ (w ++ v)).Perm (c ++ (r ++ s)) := by
  have one : (a ++ (w ++ v)).Perm ((b ++ r) ++ v) := by
    simpa only [List.append_assoc] using first.append_right v
  have two : ((b ++ r) ++ v).Perm ((b ++ v) ++ r) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := r) (l₂ := v)).append_left b
  have three := second.append_right r
  have four : ((c ++ s) ++ r).Perm (c ++ (r ++ s)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := s) (l₂ := r)).append_left c
  exact one.trans (two.trans (three.trans four))

theorem range_fold {α : Type} (state writes reads : Nat → List α) (n : Nat)
    (step : ∀ i < n, (state i ++ writes i).Perm (state (i + 1) ++ reads i)) :
    (state 0 ++ (List.range n).flatMap writes).Perm
      (state n ++ (List.range n).flatMap reads) := by
  induction n with
  | zero => simp
  | succ n previous =>
    have before := previous (fun i bound => step i (by omega))
    have last := step n (by omega)
    simpa only [List.range_succ,List.flatMap_append,List.flatMap_singleton] using
      compose (state 0) (state n) (state (n + 1))
        ((List.range n).flatMap writes) ((List.range n).flatMap reads)
        (writes n) (reads n) before last
theorem range_fin (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp

theorem finite_fold {α : Type} (n : Nat) (state : Nat → List α)
    (writes reads : Fin n → List α)
    (step : ∀ i, (state i.val ++ writes i).Perm (state (i.val + 1) ++ reads i)) :
    (state 0 ++ (List.finRange n).flatMap writes).Perm
      (state n ++ (List.finRange n).flatMap reads) := by
  let extend (f : Fin n → List α) (i : Nat) := if bound : i < n then f ⟨i,bound⟩ else []
  have sample (f : Fin n → List α) :
      (List.range n).flatMap (extend f) = (List.finRange n).flatMap f := by
    rw [← range_fin n,List.flatMap_map]
    have same : (fun i : Fin n => extend f i.val) = f := by
      funext i
      dsimp only [extend]
      rw [dif_pos i.isLt]
    rw [same]
  have complete := range_fold state (extend writes) (extend reads) n (by
    intro i bound
    simpa only [extend,dif_pos bound] using step ⟨i,bound⟩)
  simpa only [sample] using complete
end Airbender.PrefixLedgerProofs
