module
public import Proven.NonVacuous.ClockCompleteness
public import Proven.NonVacuous.HonestAttr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-! The two tactics shared by the honest rows of the span witnesses (`Blake2GSpan`, `KeccakSpan`, `KeccakSplitSpan`,
    `Blake2RoundSpan`): an equation or entry whose evaluation over the honest assignment is the cast of a natural
    identity, and a quotient entry over BabyBear. Both unfold the assignment with the `honest_column` lemmas. -/

namespace Airbender.NonVacuous

/-- An equation whose evaluation over the honest assignment is, up to `ring`, the cast of a natural identity `e` in
    `ZMod q`. -/
scoped macro "cast_identity " q:term:max e:term : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  have identity := congrArg (Nat.cast : Nat → ZMod $q) ($e)
  push_cast at identity ⊢
  linear_combination identity))

/-- A quotient entry `inverse * (sum - low)` over BabyBear, from the natural identity `sum = low + 2^k * quotient`. -/
scoped macro "quotient " inverse:term:max e:term : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  have identity := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e)
  push_cast at identity ⊢
  linear_combination (norm := ring_nf) ($inverse : ZMod 2013265921) * identity
  reduce_mod_char))

end Airbender.NonVacuous
