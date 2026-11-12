module
public import Slop.NonVacuous.Blake2RoundSpan.FinalEval
public import Slop.NonVacuous.ClockCompleteness
public import Slop.Blake2Round.OpIndex

@[expose] public section

/-! Tactics for the honest round row's equations: a column at a literal index is its honest value (`honest_value`),
    and the equation then holds by cases on the first round, the final round, or the round. -/

namespace Airbender.NonVacuous.Blake2RoundSpan.RowInput

/-- A column below the round bits is not the round bit. -/
theorem below_bit {n m r : Nat} (below : n < m) : (n = m + r) = False := by
  simp only [eq_iff_iff, iff_false]
  omega

theorem ivWord_0 : ivWord 0 = ⟨58983, 27145⟩ := by decide +kernel
theorem ivWord_1 : ivWord 1 = ⟨44677, 47975⟩ := by decide +kernel
theorem ivWord_2 : ivWord 2 = ⟨62322, 15470⟩ := by decide +kernel
theorem ivWord_3 : ivWord 3 = ⟨62778, 42319⟩ := by decide +kernel
theorem ivWord_5 : ivWord 5 = ⟨26764, 39685⟩ := by decide +kernel
theorem ivWord_7 : ivWord 7 = ⟨52505, 23520⟩ := by decide +kernel

end Airbender.NonVacuous.Blake2RoundSpan.RowInput

namespace Airbender.NonVacuous.Blake2RoundSpan

/-- A column of the honest round row at a literal index: its range lemma (`RowInput.column_*`), then its definition. -/
scoped macro "honest_value" : tactic => `(tactic| (
  simp (disch := decide) only [Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_head,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_port,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_messagePointer,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_message,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_control,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_bits,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_flags,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_prepared,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_suffix,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_products,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_scheduled,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_columnCall,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_diagonalCall,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_finalXor,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.column_clock,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.colSlot, Airbender.NonVacuous.Blake2RoundSpan.RowInput.diagSlot,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.portLimb, Airbender.NonVacuous.Blake2RoundSpan.RowInput.limb,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.suffixLane,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.finalLimb,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.below_bit, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceMod]))

/-- An equation that depends only on whether the round is the first one. -/
scoped macro "first_round_cases " x:term:max : tactic => `(tactic| (
  by_cases first : ($x).round.val = 0 <;>
    (try simp only [Airbender.NonVacuous.Blake2RoundSpan.RowInput.lane, first, Nat.left_eq_add, ↓reduceIte,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, or_self, or_false, false_or,
      Airbender.NonVacuous.Blake2RoundSpan.RowInput.ivWord_0, Airbender.NonVacuous.Blake2RoundSpan.RowInput.ivWord_1,
      Airbender.NonVacuous.Blake2RoundSpan.RowInput.ivWord_2, Airbender.NonVacuous.Blake2RoundSpan.RowInput.ivWord_3,
      Airbender.NonVacuous.Blake2RoundSpan.RowInput.ivWord_5,
      Airbender.NonVacuous.Blake2RoundSpan.RowInput.ivWord_7]) <;>
    push_cast <;> ring))

/-- An equation that depends only on whether the round is the final one. -/
scoped macro "final_cases " x:term:max : tactic => `(tactic| (
  by_cases final : ($x).final = true <;> (try simp only [final, ↓reduceIte, Bool.false_eq_true]) <;> push_cast <;>
    ring))

/-- An equation of the control word: by cases on the round. -/
scoped macro "round_cases " x:ident : tactic => `(tactic| (
  try simp only [Airbender.NonVacuous.Blake2RoundSpan.RowInput.control,
    Airbender.NonVacuous.Blake2RoundSpan.RowInput.final]
  obtain ⟨⟨r, bound⟩, _, _, _, _, _, _, _⟩ := $x
  simp only
  interval_cases r <;> norm_num))

/-- A Boolean honest column: its unfolded value is 0 or 1. -/
scoped macro "bit_value" : tactic => `(tactic| (
  honest_value
  first | omega | (split <;> omega) | simp))

end Airbender.NonVacuous.Blake2RoundSpan
