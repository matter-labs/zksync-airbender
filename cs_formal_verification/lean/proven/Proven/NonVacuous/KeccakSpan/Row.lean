module
public import Proven.NonVacuous.KeccakSpan.Asserts
public import Proven.NonVacuous.SpanTactics
public import Proven.NonVacuous.KeccakSpan.Queries
public import Mathlib.Tactic.ReduceModChar
public import Proven.Defs.Circuits.Keccak.Artifact

@[expose] public section

/-! A Keccak row's honest assignment of valid inputs satisfies its clock constraints (`Keccak.clockConstraints`
    over the modeled setup, BabyBear): the 187 assertions (`Asserts.lean`), the 42 lookups (the pointer alignment,
    the controller query at the read control word, the forty byte and rotation queries of `Queries.lean`) and the
    30 timestamp queries (the invocation clock, the two clock queries of each of the fourteen ports
    (`port_clock_contains`) and the pointer alignment). -/

namespace Airbender.NonVacuous.KeccakSpan
open Templates

variable {p : Nat} [Fact p.Prime]

set_option hygiene false in
/-- The pointer alignment query: the low limb is 256 times a timestamp-range quotient. -/
local macro "pointer" : tactic => `(tactic| (
  obtain ⟨lo, -, aligned⟩ := valid.pointer
  refine range_of_eval (n := x.pointer.lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
  quotient (-7864320) (show x.pointer.lo = 256 * (x.pointer.lo / 256) by omega)))

/-- The low previous clock of port `k`. -/
theorem clock_low (x : RowInput) {k : Nat} (hk : k < 14) :
    x.assignment (p := p) (222 + 3 * k) = ((x.previous k : Nat) : ZMod p) := by
  simp only [RowInput.assignment, RowInput.column, show ¬222 + 3 * k < 15 by omega, show ¬222 + 3 * k < 63 by omega,
    show ¬222 + 3 * k < 102 by omega, show ¬222 + 3 * k < 222 by omega, show 222 + 3 * k < 264 by omega,
    show (222 + 3 * k - 222) % 3 = 0 by omega, show (222 + 3 * k - 222) / 3 = k by omega, ↓reduceIte]

theorem clock_high (x : RowInput) {k : Nat} (hk : k < 14) :
    x.assignment (p := p) (223 + 3 * k) = ((0 : Nat) : ZMod p) := by
  simp only [RowInput.assignment, RowInput.column, show ¬223 + 3 * k < 15 by omega, show ¬223 + 3 * k < 63 by omega,
    show ¬223 + 3 * k < 102 by omega, show ¬223 + 3 * k < 222 by omega, show 223 + 3 * k < 264 by omega,
    show (223 + 3 * k - 222) % 3 = 1 by omega, ↓reduceIte, Nat.reduceEqDiff]

theorem clock_borrow (x : RowInput) {k : Nat} (hk : k < 14) : x.assignment (p := p) (224 + 3 * k) = 1 := by
  simp only [RowInput.assignment, RowInput.column, show ¬224 + 3 * k < 15 by omega, show ¬224 + 3 * k < 63 by omega,
    show ¬224 + 3 * k < 102 by omega, show ¬224 + 3 * k < 222 by omega, show 224 + 3 * k < 264 by omega,
    show (224 + 3 * k - 222) % 3 = 2 by omega, ↓reduceIte, Nat.reduceEqDiff,
    Nat.cast_one]

/-- A lane index entry: the honest column is the controller row's. -/
local macro "index" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column, RowInput.indices]
  push_cast
  ring))

theorem packed_lt (x : RowInput) : x.state.packed < 2048 := by
  have := x.state.mode.isLt
  have := x.state.iteration.isLt
  have := x.state.round.isLt
  simp only [Keccak.ControlState.packed]
  omega

/-- The controller query in the imported shape: the key, the six lane indices and the tag. -/
private theorem control_at {control : Fin 4096 → Vector Nat 6} {e0 e1 e2 e3 e4 e5 e6 e7 : Expression (ZMod p)}
    {env : Environment (ZMod p)} (key : Fin 4096) (v0 : e0.eval env = (key.val : ZMod p))
    (v1 : e1.eval env = ((control key)[0] : ZMod p)) (v2 : e2.eval env = ((control key)[1] : ZMod p))
    (v3 : e3.eval env = ((control key)[2] : ZMod p)) (v4 : e4.eval env = ((control key)[3] : ZMod p))
    (v5 : e5.eval env = ((control key)[4] : ZMod p)) (v6 : e6.eval env = ((control key)[5] : ZMod p))
    (v7 : e7.eval env = ((37 : Nat) : ZMod p)) :
    (Lookup.mk (Keccak.setupTable control).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7]).Contains env := by
  refine control_contains key fun j => ?_
  fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]

/-- Lookup 0: the pointer alignment. -/
theorem lookup_0 (x : RowInput) (valid : x.Valid) (hp : p = 2013265921)
    (h : 0 < (FlatOperation.lookups
      (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨0, h⟩).Contains
        (Verification.environment x.assignment) := by
  subst hp
  op_index
  pointer

/-- Lookup 1: the controller query at the read control word (active). -/
theorem lookup_1 (x : RowInput) (hp : p = 2013265921)
    (h : 1 < (FlatOperation.lookups
      (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨1, h⟩).Contains
        (Verification.environment x.assignment) := by
  subst hp
  op_index
  have key : (Fin.ofNat 4096 (x.state.packed + 2048)).val = x.state.packed + 2048 := by
    simp only [Fin.val_ofNat]
    have := packed_lt x
    omega
  refine control_at (Fin.ofNat 4096 (x.state.packed + 2048)) ?_ (by index) (by index) (by index) (by index)
    (by index) (by index) (by simp only [Expression.eval]; push_cast; ring)
  simp only [Expression.eval, Verification.environment, honest_column, key]
  push_cast
  ring

/-- Lookups 2 to 11: byte and rotation queries. -/
private theorem queries_0 (x : RowInput) (valid : x.Valid) (i : Nat) (low : 2 ≤ i) (high : i < 12)
    (h : i < (FlatOperation.lookups
      (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  interval_cases i
  · exact query_2 x valid h
  · exact query_3 x valid h
  · exact query_4 x valid h
  · exact query_5 x valid h
  · exact query_6 x valid h
  · exact query_7 x valid h
  · exact query_8 x valid h
  · exact query_9 x valid h
  · exact query_10 x valid h
  · exact query_11 x valid h

/-- Lookups 12 to 21: byte and rotation queries. -/
private theorem queries_1 (x : RowInput) (valid : x.Valid) (i : Nat) (low : 12 ≤ i) (high : i < 22)
    (h : i < (FlatOperation.lookups
      (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  interval_cases i
  · exact query_12 x valid h
  · exact query_13 x valid h
  · exact query_14 x valid h
  · exact query_15 x valid h
  · exact query_16 x valid h
  · exact query_17 x valid h
  · exact query_18 x valid h
  · exact query_19 x valid h
  · exact query_20 x valid h
  · exact query_21 x valid h

/-- Lookups 22 to 31: byte and rotation queries. -/
private theorem queries_2 (x : RowInput) (valid : x.Valid) (i : Nat) (low : 22 ≤ i) (high : i < 32)
    (h : i < (FlatOperation.lookups
      (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  interval_cases i
  · exact query_22 x valid h
  · exact query_23 x valid h
  · exact query_24 x valid h
  · exact query_25 x valid h
  · exact query_26 x valid h
  · exact query_27 x valid h
  · exact query_28 x valid h
  · exact query_29 x valid h
  · exact query_30 x valid h
  · exact query_31 x valid h

/-- Lookups 32 to 41: byte and rotation queries. -/
private theorem queries_3 (x : RowInput) (valid : x.Valid) (i : Nat) (low : 32 ≤ i) (high : i < 42)
    (h : i < (FlatOperation.lookups
      (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length) :
    ((FlatOperation.lookups (Keccak.importedConstraints
      (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  interval_cases i
  · exact query_32 x valid h
  · exact query_33 x valid h
  · exact query_34 x valid h
  · exact query_35 x valid h
  · exact query_36 x valid h
  · exact query_37 x valid h
  · exact query_38 x valid h
  · exact query_39 x valid h
  · exact query_40 x valid h
  · exact query_41 x valid h

theorem lookups (x : RowInput) (valid : x.Valid) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups
        (Keccak.importedConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows))).length),
      ((FlatOperation.lookups (Keccak.importedConstraints
        (Keccak.setupTable (p := p) Keccak.Controller.rows))).get ⟨i, h⟩).Contains
          (Verification.environment x.assignment) := by
  intro i h
  have size : i < 42 := by rwa [Keccak.lookup_count] at h
  rcases Nat.lt_or_ge i 2 with small | large
  · interval_cases i
    · exact lookup_0 x valid hp h
    · exact lookup_1 x hp h
  rcases Nat.lt_or_ge i 12 with first | large
  · exact queries_0 x valid i large first h
  rcases Nat.lt_or_ge i 22 with second | large
  · exact queries_1 x valid i large second h
  rcases Nat.lt_or_ge i 32 with third | large
  · exact queries_2 x valid i large third h
  · exact queries_3 x valid i large size h

theorem timestamps (x : RowInput) (valid : x.Valid) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups (Keccak.importedConstraintsTimestampLookups (p := p))).length),
      ((FlatOperation.lookups (Keccak.importedConstraintsTimestampLookups (p := p))).get ⟨i, h⟩).Contains
        (Verification.environment x.assignment) := by
  subst hp
  have room := valid.room
  have invocation := valid.invocation
  simp only [Trace.timestampBase] at room
  have port (k : Nat) (hk : k < 14) := port_clock_contains (p := 2013265921) (by decide)
    (columns := #v[222 + 3 * k, 223 + 3 * k])
    (borrow := 224 + 3 * k) (t := x.invocation) (high := 0) (q := x.previous k) (RowInput.assignment_1 x)
    (RowInput.assignment_2 x) (clock_low x hk) (clock_high x hk) (clock_borrow x hk) (valid.previous k hk)
    (by simp only [Trace.timestampBase]; omega)
  intro i h
  have size : i < 30 := by rwa [Keccak.timestamp_count] at h
  interval_cases i <;> op_index
  · refine range_of_eval (n := x.invocation / 4) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient 1509949441 (show x.invocation = 1 + 4 * (x.invocation / 4) by omega)
  · exact (port 0 (by decide)).1
  · exact (port 0 (by decide)).2
  · exact (port 1 (by decide)).1
  · exact (port 1 (by decide)).2
  · exact (port 2 (by decide)).1
  · exact (port 2 (by decide)).2
  · exact (port 3 (by decide)).1
  · exact (port 3 (by decide)).2
  · exact (port 4 (by decide)).1
  · exact (port 4 (by decide)).2
  · exact (port 5 (by decide)).1
  · exact (port 5 (by decide)).2
  · exact (port 6 (by decide)).1
  · exact (port 6 (by decide)).2
  · exact (port 7 (by decide)).1
  · exact (port 7 (by decide)).2
  · exact (port 8 (by decide)).1
  · exact (port 8 (by decide)).2
  · exact (port 9 (by decide)).1
  · exact (port 9 (by decide)).2
  · exact (port 10 (by decide)).1
  · exact (port 10 (by decide)).2
  · exact (port 11 (by decide)).1
  · exact (port 11 (by decide)).2
  · exact (port 12 (by decide)).1
  · exact (port 12 (by decide)).2
  · exact (port 13 (by decide)).1
  · exact (port 13 (by decide)).2
  · pointer

/-- The honest assignment of valid inputs satisfies the Keccak row's clock constraints over the modeled setup. -/
theorem holds (x : RowInput) (valid : x.Valid) (hp : p = 2013265921) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment x.assignment)
      (Keccak.clockConstraints (Keccak.setupTable (p := p) Keccak.Controller.rows)) := by
  refine Verification.holds_append (holds_of_get (asserts x _) (lookups x valid hp))
    (holds_of_get (fun i h => ?_) (timestamps x valid hp))
  have empty : FlatOperation.constraints (Keccak.importedConstraintsTimestampLookups (p := p)) = [] := rfl
  rw [empty] at h
  exact absurd h (Nat.not_lt_zero i)

end Airbender.NonVacuous.KeccakSpan
