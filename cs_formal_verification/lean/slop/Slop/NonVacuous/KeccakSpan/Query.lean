module
public import Slop.NonVacuous.KeccakSpan.Valid
public import Slop.NonVacuous.ClockCompleteness

@[expose] public section

/-! The shape of an operation's lookups in the imported Keccak constraints: three entries, four zeros and the tag. -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

/-- An operation's lookup `t` in the imported shape. -/
theorem query_at {o : Op} (valid : o.Valid) {control : Fin 4096 → Vector Nat 6} {t : Nat} (ht : t < 8)
    {e0 e1 e2 z3 z4 z5 z6 e7 : Expression (ZMod p)} {env : Environment (ZMod p)}
    (v0 : e0.eval env = (o.a t : ZMod p)) (v1 : e1.eval env = (o.b t : ZMod p))
    (v2 : e2.eval env = (o.c t : ZMod p))
    (zeros : z3.eval env = 0 ∧ z4.eval env = 0 ∧ z5.eval env = 0 ∧ z6.eval env = 0)
    (v7 : e7.eval env = (o.tagValue : ZMod p)) :
    (Lookup.mk (Keccak.setupTable control).toRaw #v[e0, e1, e2, z3, z4, z5, z6, e7]).Contains env := by
  refine valid.contains ht fun j => ?_
  fin_cases j <;> simp [v0, v1, v2, zeros, v7]

set_option hygiene false in
/-- A lookup entry that is one column. -/
macro "direct" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  ring))

/-- The four zero entries. -/
macro "zeros" : tactic => `(tactic| (
  simp only [Expression.eval]
  push_cast
  simp only [add_zero, and_self]))

set_option hygiene false in
/-- The tag entry of operation `k` (`RowInput.opk`), mode by mode. -/
macro "tag " k:ident : tactic => `(tactic| (
  rcases RowInput.modes x with hm | hm | hm | hm | hm | hm | hm <;>
  simp only [Expression.eval, Verification.environment, honest_column, $k:ident, hm, ↓reduceIte,
    Nat.reduceEqDiff, Op.byte_tag, Op.rotate_tag] <;>
  push_cast <;> ring))

end Airbender.NonVacuous.KeccakSpan
