module
public import Slop.Templates
public import Slop.Delegation.ClockFacts

@[expose] public section

/-!
The timestamp comparison of one delegation memory port, from its imported Boolean borrow
constraint and its two range queries (offset 2, invocation columns 1 and 2), proven once for every
port of every delegation circuit that has this layout.
-/

namespace Airbender.Delegation.Proofs
open Templates
set_option warningAsError true

/-- The low-limb comparison query: `-2 - w 1 + w previous + 2^19 * w borrow`. -/
abbrev clockLower {p : Nat} (previous borrow : Nat) : Expression (ZMod p) :=
  sumFrom (constant (Int.ofNat 0)) [constant (Int.negSucc 1),
    product (constant (Int.negSucc 0)) (cell 1), product (constant (Int.ofNat 1)) (cell previous),
    product (constant (Int.ofNat 524288)) (cell borrow)]

/-- The high-limb comparison query: `2^19 - w 2 + w previous - w borrow`. -/
abbrev clockUpper {p : Nat} (previous borrow : Nat) : Expression (ZMod p) :=
  sumFrom (constant (Int.ofNat 0)) [constant (Int.ofNat 524288),
    product (constant (Int.negSucc 0)) (cell 2), product (constant (Int.ofNat 1)) (cell previous),
    product (constant (Int.negSucc 0)) (cell borrow)]

theorem port_comparison {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {ops queries : List (FlatOperation (ZMod p))}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) ops)
    (timestamps : FlatOperation.ConstraintsHoldFlat (Verification.environment w) queries)
    {columns : ClockColumns} (invocation : columns.invocation = #v[1, 2])
    (port : Trace.TimestampPort) (offset : port.offset = 2)
    {k : Nat} {hk : k < (FlatOperation.constraints ops).length}
    (bit : (FlatOperation.constraints ops).get ⟨k, hk⟩ = flag port.borrow)
    {a : Nat} {ha : a < (FlatOperation.lookups queries).length}
    (lower : (FlatOperation.lookups queries).get ⟨a, ha⟩ =
      Trace.timestampLookup (clockLower port.previous[0] port.borrow))
    {b : Nat} {hb : b < (FlatOperation.lookups queries).length}
    (upper : (FlatOperation.lookups queries).get ⟨b, hb⟩ =
      Trace.timestampLookup (clockUpper port.previous[1] port.borrow)) :
    w port.borrow * (w port.borrow - 1) = 0 ∧
    ((w port.previous[0] - w columns.invocation[0] - port.offset +
      Trace.timestampBase * w port.borrow) : ZMod p).val < Trace.timestampBase ∧
    ((w port.previous[1] + Trace.timestampBase - w port.borrow -
      w columns.invocation[1]) : ZMod p).val < Trace.timestampBase := by
  have flag := flag_bit core bit
  have low := Verification.lookup_of_holds timestamps ⟨a, ha⟩
  have high := Verification.lookup_of_holds timestamps ⟨b, hb⟩
  rw [lower] at low
  rw [upper] at high
  replace low := Trace.Proofs.range_bound low
  replace high := Trace.Proofs.range_bound high
  simp only [List.foldl, Expression.eval, Verification.environment] at low high
  push_cast at low high
  simp only [invocation, offset, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_⟩
  · rcases flag with zero | one
    · rw [zero, zero_mul]
    · rw [one, sub_self, mul_zero]
  · convert low using 2
    simp only [Trace.timestampBase]
    push_cast
    ring
  · convert high using 2
    simp only [Trace.timestampBase]
    push_cast
    ring

end Airbender.Delegation.Proofs
