module
public import Slop.NonVacuous.ClockCompleteness
public import Slop.NonVacuous.HonestAttr
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-! Two tactics for the honest split-Keccak rows: an entry or equation that is the cast of a natural identity, and
    a quotient entry over BabyBear (the shape of `Slop/NonVacuous/Blake2GSpan/Lookups.lean`'s `quotient`). -/

namespace Airbender.NonVacuous.KeccakSplitSpan

/-- An equation whose evaluation over the honest assignment is, up to `ring`, the cast of a natural identity `e`
    in `ZMod q`. -/
macro "cast_identity " q:term:max e:term : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  have identity := congrArg (Nat.cast : Nat → ZMod $q) ($e)
  push_cast at identity ⊢
  linear_combination identity))

/-- A quotient entry `inverse * (sum - low)` over BabyBear, from the natural identity `sum = low + 2^k * quotient`. -/
macro "quotient_entry " inverse:term:max e:term : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  have identity := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e)
  push_cast at identity ⊢
  linear_combination (norm := ring_nf) ($inverse : ZMod 2013265921) * identity
  reduce_mod_char))

end Airbender.NonVacuous.KeccakSplitSpan
