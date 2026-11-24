module
public import Proven.Delegation.ClockShapes
public import Proven.Trace.Timestamps
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Completeness helpers shared by the non-vacuity witnesses of the delegation families: `ConstraintsHoldFlat` from
    its asserts and lookups by index (the converse of `Verification.assertion_of_holds`/`lookup_of_holds`), Boolean
    flags, timestamp range queries, and the clock comparison of one delegation memory port (the shape of
    `Delegation.Proofs.port_comparison`: offset 2, invocation clock in columns 1 and 2) for an honest port. -/

namespace Airbender.NonVacuous
open Templates Trace

/-- Every indexed assertion and lookup of `ops` holds. -/
theorem holds_of_get {F : Type} [Field F] {env : Environment F} {ops : List (FlatOperation F)}
    (asserts : ∀ i (h : i < (FlatOperation.constraints ops).length),
      ((FlatOperation.constraints ops).get ⟨i, h⟩).eval env = 0)
    (lookups : ∀ i (h : i < (FlatOperation.lookups ops).length),
      ((FlatOperation.lookups ops).get ⟨i, h⟩).Contains env) :
    FlatOperation.ConstraintsHoldFlat env ops := by
  refine FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr ⟨fun e member => ?_, fun l member => ?_⟩
  · obtain ⟨⟨i, h⟩, rfl⟩ := List.get_of_mem member
    exact asserts i h
  · obtain ⟨⟨i, h⟩, rfl⟩ := List.get_of_mem member
    exact lookups i h

variable {p : Nat} [Fact p.Prime]

/-- The Boolean constraint of a column holding 0 or 1. -/
theorem flag_eval {w : Nat → ZMod p} {k n : Nat} (column : w k = (n : ZMod p)) (bit : n ≤ 1) :
    (flag k : Expression (ZMod p)).eval (Verification.environment w) = 0 := by
  simp only [Expression.eval, Verification.environment, column]
  interval_cases n <;> push_cast <;> ring

/-- A timestamp range query whose entry evaluates to a small natural number. -/
theorem range_of_eval {e : Expression (ZMod p)} {env : Environment (ZMod p)} {n : Nat}
    (value : e.eval env = (n : ZMod p)) (bound : n < timestampBase) (room : timestampBase ≤ p) :
    (timestampLookup e).Contains env :=
  Proofs.range_contains (by rw [value, ZMod.val_natCast_of_lt (by omega)]; exact bound)

/-- One delegation port's two clock queries, for borrow 1, equal high clock limbs, and a previous low clock below
    the write clock (invocation + 2) by at most one limb. -/
theorem port_clock_contains (room : timestampBase ≤ p) {w : Nat → ZMod p} {columns : Vector Nat 2}
    {borrow : Nat} {t high q : Nat} (invocationLow : w 1 = (t : ZMod p))
    (invocationHigh : w 2 = (high : ZMod p)) (previousLow : w columns[0] = (q : ZMod p))
    (previousHigh : w columns[1] = (high : ZMod p)) (bit : w borrow = 1) (before : q < t + 2)
    (near : t + 2 ≤ q + timestampBase) :
    (timestampLookup (Delegation.Proofs.clockLower columns[0] borrow)).Contains
        (Verification.environment w) ∧
      (timestampLookup (Delegation.Proofs.clockUpper columns[1] borrow)).Contains
        (Verification.environment w) := by
  refine ⟨range_of_eval (n := q + timestampBase - (t + 2)) ?_ (by omega) room,
    range_of_eval (n := timestampBase - 1) ?_ (by decide) room⟩
  · simp only [Delegation.Proofs.clockLower, sumFrom, List.foldl, Expression.eval, Verification.environment,
      invocationLow, previousLow, bit]
    rw [Nat.cast_sub near]
    push_cast
    ring
  · simp only [Delegation.Proofs.clockUpper, sumFrom, List.foldl, Expression.eval, Verification.environment,
      invocationHigh, previousHigh, bit]
    push_cast
    ring

end Airbender.NonVacuous
