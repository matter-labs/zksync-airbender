import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

def blocksLength (blocks : List Block) : Nat := (blocks.map Block.length).sum

/-- Compare equal encoded blocks directly; at a differently compressed short
    tail, compare every actual cell. No table formula participates. -/
def blocksAgree : List Block → List Block → Bool
  | [], [] => true
  | a :: left, b :: right =>
    if a = b then blocksAgree left right
    else decide (blocksLength (a :: left) ≤ 16 ∧ blocksLength (b :: right) ≤ 16) &&
      (List.finRange 16).all (fun n =>
        getFromBlocks (a :: left) n.val == getFromBlocks (b :: right) n.val)
  | _, _ => false

private theorem after_end (blocks : List Block) (n : Nat) (outside : blocksLength blocks ≤ n) :
    getFromBlocks blocks n = none := by
  induction blocks generalizing n with
  | nil => rfl
  | cons block rest ih =>
    simp only [blocksLength, List.map_cons, List.sum_cons] at outside
    rw [getFromBlocks, if_neg (by omega)]
    exact ih _ (by dsimp [blocksLength]; omega)

theorem blocksAgree_sound (left right : List Block) (checked : blocksAgree left right = true)
    (n : Nat) : getFromBlocks left n = getFromBlocks right n := by
  induction left generalizing right n with
  | nil =>
    cases right with
    | nil => rfl
    | cons b bs => simp [blocksAgree] at checked
  | cons a left ih =>
    cases right with
    | nil => simp [blocksAgree] at checked
    | cons b right =>
      by_cases equal : a = b
      · subst b
        have rest : blocksAgree left right = true := by
          simpa only [blocksAgree, if_true] using checked
        simp only [getFromBlocks]
        split
        · rfl
        · exact ih _ rest _
      · simp only [blocksAgree, if_neg equal, Bool.and_eq_true, decide_eq_true_eq] at checked
        by_cases small : n < 16
        · have sample := List.all_eq_true.mp checked.2 ⟨n, small⟩ (by simp)
          simpa only [beq_iff_eq] using sample
        · rw [after_end _ n (by have := checked.1.1; omega),
            after_end _ n (by have := checked.1.2; omega)]

end Airbender.Setup.Proofs
