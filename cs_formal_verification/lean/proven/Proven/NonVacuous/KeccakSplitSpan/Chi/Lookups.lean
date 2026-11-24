module
public import Proven.NonVacuous.KeccakSplitSpan.Chi.Honest
public import Proven.NonVacuous.KeccakSplitSpan.Chi.Tables
public import Proven.NonVacuous.SpanTactics
public import Proven.KeccakSplit.Chi5.OpIndex

@[expose] public section

/-! The 18 imported lookups of a chi row hold for the honest assignment of valid inputs, over BabyBear: the pointer
    alignment, the control query of the call, and the sixteen chi queries at the read nibbles. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Chi
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- An entry whose evaluation is the honest value. -/
local macro "chi_direct" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column, RowInput.control, plane]
  try push_cast
  try ring))

/-- A chi result entry: the honest column is chi of the read nibbles by definition. -/
local macro "chi_result" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  simp only [zero_add, one_mul]
  rfl))

variable {p : Nat} [Fact p.Prime]

theorem lookups (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .chi5) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups (Chi5.importedConstraints (Chi5.setup (p := p)))).length),
      ((FlatOperation.lookups (Chi5.importedConstraints (Chi5.setup (p := p)))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment x)) := by
  subst hp
  have lane (l : Nat) (m : Nat) (small : l < 5 := by decide) := valid.limb (l := l) (by rw [kind]; exact small) m
  have pointer := valid.pointer
  simp only [Word.Bounded, limbBase] at pointer
  intro i h
  have size : i < 18 := by
    have count : (FlatOperation.lookups (Chi5.importedConstraints
      (Chi5.setup (p := 2013265921)))).length = 18 := by rfl
    omega
  interval_cases i <;> op_index
  · refine range_of_eval (n := (x.read 1).lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient (-7864320) (show (x.read 1).lo = 256 * ((x.read 1).lo / 256) by omega)
  · exact control_at valid.call kind (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 0) 0) (a1 := nib (x.limb 1 0) 0) (a2 := nib (x.limb 2 0) 0)
      (a3 := nib (x.limb 3 0) 0) (a4 := nib (x.limb 4 0) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 0) 1) (a1 := nib (x.limb 1 0) 1) (a2 := nib (x.limb 2 0) 1)
      (a3 := nib (x.limb 3 0) 1) (a4 := nib (x.limb 4 0) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 0) 2) (a1 := nib (x.limb 1 0) 2) (a2 := nib (x.limb 2 0) 2)
      (a3 := nib (x.limb 3 0) 2) (a4 := nib (x.limb 4 0) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 0) 3) (a1 := nib (x.limb 1 0) 3) (a2 := nib (x.limb 2 0) 3)
      (a3 := nib (x.limb 3 0) 3) (a4 := nib (x.limb 4 0) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (lane 0 0)).1)
      (by quotient (-491520) (nib_limb (lane 1 0)).1)
      (by quotient (-491520) (nib_limb (lane 2 0)).1)
      (by quotient (-491520) (nib_limb (lane 3 0)).1)
      (by quotient (-491520) (nib_limb (lane 4 0)).1)
      (by quotient (-491520) (show out x 0 0 = chiNib x 0 0 + 16 * chiNib x 0 1 +
        256 * chiNib x 0 2 + 4096 * chi4 (nib (x.limb 0 0) 3) (nib (x.limb 1 0) 3) (nib (x.limb 2 0) 3)
        from rfl))
      (by quotient (-491520) (show out x 1 0 = chiNib x 1 0 + 16 * chiNib x 1 1 +
        256 * chiNib x 1 2 + 4096 * chi4 (nib (x.limb 1 0) 3) (nib (x.limb 2 0) 3) (nib (x.limb 3 0) 3)
        from rfl))
      (by quotient (-491520) (show out x 2 0 = chiNib x 2 0 + 16 * chiNib x 2 1 +
        256 * chiNib x 2 2 + 4096 * chi4 (nib (x.limb 2 0) 3) (nib (x.limb 3 0) 3) (nib (x.limb 4 0) 3)
        from rfl))
      (by quotient (-491520) (show out x 3 0 = chiNib x 3 0 + 16 * chiNib x 3 1 +
        256 * chiNib x 3 2 + 4096 * chi4 (nib (x.limb 3 0) 3) (nib (x.limb 4 0) 3) (nib (x.limb 0 0) 3)
        from rfl))
      (by quotient (-491520) (show out x 4 0 = chiNib x 4 0 + 16 * chiNib x 4 1 +
        256 * chiNib x 4 2 + 4096 * chi4 (nib (x.limb 4 0) 3) (nib (x.limb 0 0) 3) (nib (x.limb 1 0) 3)
        from rfl))
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 1) 0) (a1 := nib (x.limb 1 1) 0) (a2 := nib (x.limb 2 1) 0)
      (a3 := nib (x.limb 3 1) 0) (a4 := nib (x.limb 4 1) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 1) 1) (a1 := nib (x.limb 1 1) 1) (a2 := nib (x.limb 2 1) 1)
      (a3 := nib (x.limb 3 1) 1) (a4 := nib (x.limb 4 1) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 1) 2) (a1 := nib (x.limb 1 1) 2) (a2 := nib (x.limb 2 1) 2)
      (a3 := nib (x.limb 3 1) 2) (a4 := nib (x.limb 4 1) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 1) 3) (a1 := nib (x.limb 1 1) 3) (a2 := nib (x.limb 2 1) 3)
      (a3 := nib (x.limb 3 1) 3) (a4 := nib (x.limb 4 1) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (lane 0 1)).1)
      (by quotient (-491520) (nib_limb (lane 1 1)).1)
      (by quotient (-491520) (nib_limb (lane 2 1)).1)
      (by quotient (-491520) (nib_limb (lane 3 1)).1)
      (by quotient (-491520) (nib_limb (lane 4 1)).1)
      (by quotient (-491520) (show out x 0 1 = chiNib x 0 4 + 16 * chiNib x 0 5 +
        256 * chiNib x 0 6 + 4096 * chi4 (nib (x.limb 0 1) 3) (nib (x.limb 1 1) 3) (nib (x.limb 2 1) 3)
        from rfl))
      (by quotient (-491520) (show out x 1 1 = chiNib x 1 4 + 16 * chiNib x 1 5 +
        256 * chiNib x 1 6 + 4096 * chi4 (nib (x.limb 1 1) 3) (nib (x.limb 2 1) 3) (nib (x.limb 3 1) 3)
        from rfl))
      (by quotient (-491520) (show out x 2 1 = chiNib x 2 4 + 16 * chiNib x 2 5 +
        256 * chiNib x 2 6 + 4096 * chi4 (nib (x.limb 2 1) 3) (nib (x.limb 3 1) 3) (nib (x.limb 4 1) 3)
        from rfl))
      (by quotient (-491520) (show out x 3 1 = chiNib x 3 4 + 16 * chiNib x 3 5 +
        256 * chiNib x 3 6 + 4096 * chi4 (nib (x.limb 3 1) 3) (nib (x.limb 4 1) 3) (nib (x.limb 0 1) 3)
        from rfl))
      (by quotient (-491520) (show out x 4 1 = chiNib x 4 4 + 16 * chiNib x 4 5 +
        256 * chiNib x 4 6 + 4096 * chi4 (nib (x.limb 4 1) 3) (nib (x.limb 0 1) 3) (nib (x.limb 1 1) 3)
        from rfl))
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 2) 0) (a1 := nib (x.limb 1 2) 0) (a2 := nib (x.limb 2 2) 0)
      (a3 := nib (x.limb 3 2) 0) (a4 := nib (x.limb 4 2) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 2) 1) (a1 := nib (x.limb 1 2) 1) (a2 := nib (x.limb 2 2) 1)
      (a3 := nib (x.limb 3 2) 1) (a4 := nib (x.limb 4 2) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 2) 2) (a1 := nib (x.limb 1 2) 2) (a2 := nib (x.limb 2 2) 2)
      (a3 := nib (x.limb 3 2) 2) (a4 := nib (x.limb 4 2) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 2) 3) (a1 := nib (x.limb 1 2) 3) (a2 := nib (x.limb 2 2) 3)
      (a3 := nib (x.limb 3 2) 3) (a4 := nib (x.limb 4 2) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (lane 0 2)).1)
      (by quotient (-491520) (nib_limb (lane 1 2)).1)
      (by quotient (-491520) (nib_limb (lane 2 2)).1)
      (by quotient (-491520) (nib_limb (lane 3 2)).1)
      (by quotient (-491520) (nib_limb (lane 4 2)).1)
      (by quotient (-491520) (show out x 0 2 = chiNib x 0 8 + 16 * chiNib x 0 9 +
        256 * chiNib x 0 10 + 4096 * chi4 (nib (x.limb 0 2) 3) (nib (x.limb 1 2) 3) (nib (x.limb 2 2) 3)
        from rfl))
      (by quotient (-491520) (show out x 1 2 = chiNib x 1 8 + 16 * chiNib x 1 9 +
        256 * chiNib x 1 10 + 4096 * chi4 (nib (x.limb 1 2) 3) (nib (x.limb 2 2) 3) (nib (x.limb 3 2) 3)
        from rfl))
      (by quotient (-491520) (show out x 2 2 = chiNib x 2 8 + 16 * chiNib x 2 9 +
        256 * chiNib x 2 10 + 4096 * chi4 (nib (x.limb 2 2) 3) (nib (x.limb 3 2) 3) (nib (x.limb 4 2) 3)
        from rfl))
      (by quotient (-491520) (show out x 3 2 = chiNib x 3 8 + 16 * chiNib x 3 9 +
        256 * chiNib x 3 10 + 4096 * chi4 (nib (x.limb 3 2) 3) (nib (x.limb 4 2) 3) (nib (x.limb 0 2) 3)
        from rfl))
      (by quotient (-491520) (show out x 4 2 = chiNib x 4 8 + 16 * chiNib x 4 9 +
        256 * chiNib x 4 10 + 4096 * chi4 (nib (x.limb 4 2) 3) (nib (x.limb 0 2) 3) (nib (x.limb 1 2) 3)
        from rfl))
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 3) 0) (a1 := nib (x.limb 1 3) 0) (a2 := nib (x.limb 2 3) 0)
      (a3 := nib (x.limb 3 3) 0) (a4 := nib (x.limb 4 3) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 3) 1) (a1 := nib (x.limb 1 3) 1) (a2 := nib (x.limb 2 3) 1)
      (a3 := nib (x.limb 3 3) 1) (a4 := nib (x.limb 4 3) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 3) 2) (a1 := nib (x.limb 1 3) 2) (a2 := nib (x.limb 2 3) 2)
      (a3 := nib (x.limb 3 3) 2) (a4 := nib (x.limb 4 3) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct) (by chi_direct)
      (by chi_result) (by chi_result) (by chi_result) (by chi_result) (by chi_result)
      (by chi_direct)
  · exact chi_at (a0 := nib (x.limb 0 3) 3) (a1 := nib (x.limb 1 3) 3) (a2 := nib (x.limb 2 3) 3)
      (a3 := nib (x.limb 3 3) 3) (a4 := nib (x.limb 4 3) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (lane 0 3)).1)
      (by quotient (-491520) (nib_limb (lane 1 3)).1)
      (by quotient (-491520) (nib_limb (lane 2 3)).1)
      (by quotient (-491520) (nib_limb (lane 3 3)).1)
      (by quotient (-491520) (nib_limb (lane 4 3)).1)
      (by quotient (-491520) (show out x 0 3 = chiNib x 0 12 + 16 * chiNib x 0 13 +
        256 * chiNib x 0 14 + 4096 * chi4 (nib (x.limb 0 3) 3) (nib (x.limb 1 3) 3) (nib (x.limb 2 3) 3)
        from rfl))
      (by quotient (-491520) (show out x 1 3 = chiNib x 1 12 + 16 * chiNib x 1 13 +
        256 * chiNib x 1 14 + 4096 * chi4 (nib (x.limb 1 3) 3) (nib (x.limb 2 3) 3) (nib (x.limb 3 3) 3)
        from rfl))
      (by quotient (-491520) (show out x 2 3 = chiNib x 2 12 + 16 * chiNib x 2 13 +
        256 * chiNib x 2 14 + 4096 * chi4 (nib (x.limb 2 3) 3) (nib (x.limb 3 3) 3) (nib (x.limb 4 3) 3)
        from rfl))
      (by quotient (-491520) (show out x 3 3 = chiNib x 3 12 + 16 * chiNib x 3 13 +
        256 * chiNib x 3 14 + 4096 * chi4 (nib (x.limb 3 3) 3) (nib (x.limb 4 3) 3) (nib (x.limb 0 3) 3)
        from rfl))
      (by quotient (-491520) (show out x 4 3 = chiNib x 4 12 + 16 * chiNib x 4 13 +
        256 * chiNib x 4 14 + 4096 * chi4 (nib (x.limb 4 3) 3) (nib (x.limb 0 3) 3) (nib (x.limb 1 3) 3)
        from rfl))
      (by chi_direct)

end Airbender.NonVacuous.KeccakSplitSpan.Chi
