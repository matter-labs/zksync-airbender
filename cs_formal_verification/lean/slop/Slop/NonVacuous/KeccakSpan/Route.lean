module
public import Slop.NonVacuous.KeccakSpan.Honest
public import Slop.Keccak.OpIndex
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The routing assertions of a Keccak row hold mode by mode: once the mode (and, for Rho, the iteration) is
    fixed, every flag is 0 or 1 and an assertion is the cast of the identity between an operation's entries and
    the operands or results it routes (`route`). A byte entry `n % 256` is cast as `n - 256 * (n / 256)`. -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

theorem cast_mod256 (n : Nat) :
    ((n % 256 : Nat) : ZMod p) = (n : ZMod p) - 256 * ((n / 256 : Nat) : ZMod p) := by
  have identity := congrArg (Nat.cast : Nat → ZMod p) (Nat.mod_add_div n 256)
  push_cast at identity
  linear_combination identity

/-- The eleven cases of a row: a mode, and for Rho also an iteration. -/
theorem RowInput.cases (x : RowInput) :
    x.mode = 0 ∨ x.mode = 1 ∨ x.mode = 2 ∨ x.mode = 3 ∨ (x.mode = 4 ∧ x.iteration = 0) ∨
      (x.mode = 4 ∧ x.iteration = 1) ∨ (x.mode = 4 ∧ x.iteration = 2) ∨ (x.mode = 4 ∧ x.iteration = 3) ∨
      (x.mode = 4 ∧ x.iteration = 4) ∨ x.mode = 5 ∨ x.mode = 6 := by
  have mode := x.state.mode.isLt
  have iteration := x.state.iteration.isLt
  simp only [RowInput.mode, RowInput.iteration]
  omega

set_option hygiene false in
/-- Close a routing assertion of operation `k` (`RowInput.opk`) for the row `x`, case by case. -/
macro "route " k:ident : tactic => `(tactic| (
  rcases RowInput.cases x with
    hm | hm | hm | hm | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩ | hm | hm <;>
  simp only [Expression.eval, Verification.environment, honest_column, $k:ident, RowInput.written, RowInput.temp,
    Op.byte_a, Op.byte_b, Op.byte_c, Op.byte_out, Op.rotate_a, Op.rotate_b, Op.rotate_c, Op.rotate_out,
    rhoAmount_0_0, rhoAmount_0_1, rhoAmount_0_2, rhoAmount_0_3, rhoAmount_0_4, rhoAmount_1_0, rhoAmount_1_1,
    rhoAmount_1_2, rhoAmount_1_3, rhoAmount_1_4, rhoAmount_2_0, rhoAmount_2_1, rhoAmount_2_2, rhoAmount_2_3,
    rhoAmount_2_4, rhoAmount_3_0, rhoAmount_3_1, rhoAmount_3_2, rhoAmount_3_3, rhoAmount_3_4, rhoAmount_4_0,
    rhoAmount_4_1, rhoAmount_4_2, rhoAmount_4_3, rhoAmount_4_4,
    ↓reduceIte, reduceIte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceLT, Nat.reducePow, Nat.reduceMul, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, mul_one, zero_add,
    add_zero, false_and, and_false, and_self, true_and, or_self, true_or, or_true, false_or, or_false,
    cast_mod256, Int.cast_negSucc, *] <;>
  push_cast <;> ring))

/-- The seven modes of a row. -/
theorem RowInput.modes (x : RowInput) :
    x.mode = 0 ∨ x.mode = 1 ∨ x.mode = 2 ∨ x.mode = 3 ∨ x.mode = 4 ∨ x.mode = 5 ∨ x.mode = 6 := by
  have mode := x.state.mode.isLt
  simp only [RowInput.mode]
  omega

set_option hygiene false in
/-- Close a gated copy assertion `(read - written) * flag` of the row `x`, mode by mode: the flag's mode writes
    the lane back unchanged, every other mode zeroes the flag. -/
macro "copy" : tactic => `(tactic| (
  rcases RowInput.modes x with hm | hm | hm | hm | hm | hm | hm <;>
  simp only [Expression.eval, Verification.environment, honest_column, RowInput.written, ↓reduceIte, reduceIte,
    Nat.reduceEqDiff, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, false_or, or_false, or_self, true_or,
    or_true, Int.cast_negSucc, *] <;>
  ring))

end Airbender.NonVacuous.KeccakSpan
