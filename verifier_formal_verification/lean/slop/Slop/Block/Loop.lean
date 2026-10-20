import Slop.RV.Jal
import Slop.RV.CopyRun

/-! # Loops of blocks

A loop is an induction over its remaining count `k`: `Inv k S` says the loop head `S` has `k` iterations left.
`run_loop` runs `k` iterations (each a machine run with a frame relation `F`) to the exit, given one body step per
count. `codeAt_of_mem_range` carries a code image across a state change that leaves its bytes unchanged. -/

namespace RV.Block

/-- Iterating a body: from `k` remaining (`Inv k S`), the run to the exit `Exit`, related to `S` by `F` (transitive). -/
theorem run_loop {F : State → State → Prop} (hF : ∀ S S' S'', F S S' → F S' S'' → F S S'')
    {Inv : Nat → State → Prop} {Exit : State → Prop}
    (body : ∀ j S, Inv (j + 1) S → ∃ m S', run m S = some S' ∧ F S S' ∧ (j = 0 → Exit S') ∧ (0 < j → Inv j S')) :
    ∀ k S, 1 ≤ k → Inv k S → ∃ m S', run m S = some S' ∧ F S S' ∧ Exit S' := by
  intro k
  induction k with
  | zero => intros; omega
  | succ j ih =>
    intro S _ hI
    obtain ⟨m, S', hr, hF1, hE, hI'⟩ := body j S hI
    rcases Nat.eq_zero_or_pos j with hj | hj
    · exact ⟨m, S', hr, hF1, hE hj⟩
    · obtain ⟨m2, S'', hr2, hF2, hE2⟩ := ih S' hj (hI' hj)
      exact ⟨m + m2, S'', run_trans hr hr2, hF _ _ _ hF1 hF2, hE2⟩

/-- Code at `A` is unchanged when memory is unchanged over its bytes. -/
theorem codeAt_of_mem_range {S S' : State} {A : Word} {code : List Word} (hc : CodeAt S A code)
    (hr : A.toNat + 4 * code.length ≤ 2 ^ 32)
    (h : ∀ a : Word, A.toNat ≤ a.toNat → a.toNat < A.toNat + 4 * code.length → S'.mem a = S.mem a) :
    CodeAt S' A code := by
  intro i hi
  rw [← hc i hi]
  apply read_congr
  intro j hj
  apply h <;> bv_omega

end RV.Block
