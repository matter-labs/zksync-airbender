module
public import Slop.NonVacuous.Blake2GSpan.Honest
public import Slop.NonVacuous.Blake2GSpan.Tables
public import Slop.NonVacuous.ClockCompleteness
public import Slop.Blake2G.OpIndex
public import Slop.Blake2G.ArtifactChecks
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! The 21 imported lookups of a G row hold for the honest assignment of valid inputs, over BabyBear: the two
    pointer alignment queries, the controller query at the read control word, and the eighteen XOR queries, each
    at the row of its chunks. A query entry that divides by a power of two evaluates to the quotient: the cast of a
    natural identity, scaled by the power's inverse (`reduce_mod_char`). -/

namespace Airbender.NonVacuous.Blake2GSpan
open Arithmetic Templates

/-- A column entry: its evaluation is the honest value. -/
local macro "direct" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  ring))

/-- An XOR result entry: the honest column is the XOR by definition. -/
local macro "result" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  simp only [zero_add, one_mul]
  rfl))

/-- A quotient entry `inverse * (sum - low)`, from the natural identity `sum = low + 2^k * quotient`. -/
local macro "quotient " inverse:term:max e:term : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  have identity := congrArg (Nat.cast : Nat → ZMod 2013265921) ($e)
  push_cast at identity ⊢
  linear_combination (norm := ring_nf) ($inverse : ZMod 2013265921) * identity
  reduce_mod_char))

variable {p : Nat} [Fact p.Prime]

/-- XOR queries in the imported shape: three computed entries, five zeros and the region's tag. -/
private theorem xor_at {control : Fin 512 → Vector Nat 7} {e0 e1 e2 : Expression (ZMod p)}
    {env : Environment (ZMod p)} (a b : Nat) {tag : Nat}
    (region : ∀ (entry : Vector (Expression (ZMod p)) 9), (∀ j : Fin 9, entry[j].eval env =
      ((#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, tag][j] : Nat) : ZMod p)) →
        (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env)
    (v0 : e0.eval env = (a : ZMod p)) (v1 : e1.eval env = (b : ZMod p))
    (v2 : e2.eval env = ((a ^^^ b : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw
      #v[e0, e1, e2, tagEntry 0, tagEntry 0, tagEntry 0, tagEntry 0, tagEntry 0, tagEntry tag]).Contains env := by
  refine region _ fun j => ?_
  fin_cases j <;> simp [v0, v1, v2, Expression.eval]

/-- The controller query in the imported shape: the key, the seven outputs and the tag. -/
private theorem control_at {control : Fin 512 → Vector Nat 7} {e0 e1 e2 e3 e4 e5 e6 e7 : Expression (ZMod p)}
    {env : Environment (ZMod p)} (key : Fin 512) (v0 : e0.eval env = (key.val : ZMod p))
    (v1 : e1.eval env = ((control key)[0] : ZMod p)) (v2 : e2.eval env = ((control key)[1] : ZMod p))
    (v3 : e3.eval env = ((control key)[2] : ZMod p)) (v4 : e4.eval env = ((control key)[3] : ZMod p))
    (v5 : e5.eval env = ((control key)[4] : ZMod p)) (v6 : e6.eval env = ((control key)[5] : ZMod p))
    (v7 : e7.eval env = ((control key)[6] : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, tagEntry 28]).Contains env := by
  refine control_contains key fun j => ?_
  fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, Expression.eval]

theorem lookups (x : RowInput) (valid : x.Valid) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups
        (Blake2G.importedConstraints (Blake2G.setupTable (p := p) Blake2G.Control.controllerRows))).length),
      ((FlatOperation.lookups (Blake2G.importedConstraints
        (Blake2G.setupTable (p := p) Blake2G.Control.controllerRows))).get ⟨i, h⟩).Contains
          (Verification.environment x.assignment) := by
  subst hp
  have a := valid.a
  have b := valid.b
  have c := valid.c
  have d := valid.d
  have mx := valid.mx
  have my := valid.my
  have sp := valid.statePointer
  have mp := valid.messagePointer
  simp only [Word.Bounded, limbBase] at a b c d mx my sp mp
  obtain ⟨xd0, xd1, xd2, xd3, xb0, xb1, xb2, xb3, xb4, xb5, xe0, xe1, xe2, xe3, -, -, -, -⟩ := valid.xors
  intro i h
  have size : i < 21 := by rwa [Blake2G.lookup_count] at h
  interval_cases i <;> op_index
  · refine range_of_eval (n := x.statePointer.lo / 64) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient 1981808641 (show x.statePointer.lo = 64 * (x.statePointer.lo / 64) by omega)
  · refine range_of_eval (n := x.messagePointer.lo / 64) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient 1981808641 (show x.messagePointer.lo = 64 * (x.messagePointer.lo / 64) by omega)
  · have control := valid.control
    refine control_at ⟨256 + x.control % 256, by omega⟩ ?_ (by result) (by result) (by result) (by result)
      (by result) (by result) (by result)
    simp only [Expression.eval, Verification.environment, honest_column]
    push_cast
    rw [Nat.mod_eq_of_lt control]
    ring
  · exact xor_at (x.d.lo % 256) (x.a1lo % 256) (fun _ => xor8_contains (by omega) (by simp only [RowInput.a1lo]; omega)) (by direct)
      (by direct) (by result)
  · exact xor_at (x.d.lo / 256) (x.a1lo / 256) (fun _ => xor8_contains (by omega) (by simp only [RowInput.a1lo]; omega))
      (by quotient (-7864320) (show x.d.lo = x.d.lo % 256 + 256 * (x.d.lo / 256) by omega))
      (by quotient (-7864320) (show x.a.lo + x.b.lo + x.mx.lo = 65536 * (x.carryA0 % 2) +
        131072 * (x.carryA0 / 2) + x.a1lo % 256 + 256 * (x.a1lo / 256) by
          simp only [RowInput.carryA0, RowInput.a1lo, RowInput.sumA0]; omega))
      (by result)
  · exact xor_at (x.d.hi % 256) (x.a1hi % 256) (fun _ => xor8_contains (by omega) (by simp only [RowInput.a1hi]; omega)) (by direct)
      (by direct) (by result)
  · exact xor_at (x.d.hi / 256) (x.a1hi / 256) (fun _ => xor8_contains (by omega) (by simp only [RowInput.a1hi]; omega))
      (by quotient (-7864320) (show x.d.hi = x.d.hi % 256 + 256 * (x.d.hi / 256) by omega))
      (by quotient (-7864320) (show x.a.hi + x.b.hi + x.mx.hi + x.carryA0 % 2 + 2 * (x.carryA0 / 2) =
        65536 * (x.carryA1 % 2) + 131072 * (x.carryA1 / 2) + x.a1hi % 256 + 256 * (x.a1hi / 256) by
          simp only [RowInput.carryA1, RowInput.a1hi, RowInput.sumA1]; omega))
      (by result)
  · exact xor_at (x.b.lo % 8) (x.c1lo % 8) (fun _ => xor3_contains (by omega) (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.b.lo / 8 % 512) (x.c1lo / 8 % 512) (fun _ => xor9_contains (by omega) (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.b.lo / 4096) (x.c1lo / 4096) (fun _ => xor4_contains (by omega) (by simp only [RowInput.c1lo]; omega))
      (by quotient 2012774401 (show x.b.lo = x.b.lo % 8 + 8 * (x.b.lo / 8 % 512) + 4096 * (x.b.lo / 4096) by
        omega))
      (by quotient 2012774401 (show x.c.lo + x.xd2 + 256 * x.xd3 = 65536 * x.carryC0 + x.c1lo % 8 +
        8 * (x.c1lo / 8 % 512) + 4096 * (x.c1lo / 4096) by
          simp only [RowInput.carryC0, RowInput.c1lo, RowInput.sumC0, RowInput.d1lo]; omega))
      (by result)
  · exact xor_at (x.b.hi % 8) (x.c1hi % 8) (fun _ => xor3_contains (by omega) (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.b.hi / 8 % 512) (x.c1hi / 8 % 512) (fun _ => xor9_contains (by omega) (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.b.hi / 4096) (x.c1hi / 4096) (fun _ => xor4_contains (by omega) (by simp only [RowInput.c1hi]; omega))
      (by quotient 2012774401 (show x.b.hi = x.b.hi % 8 + 8 * (x.b.hi / 8 % 512) + 4096 * (x.b.hi / 4096) by
        omega))
      (by quotient 2012774401 (show x.c.hi + x.xd0 + 256 * x.xd1 + x.carryC0 = 65536 * x.carryC1 +
        x.c1hi % 8 + 8 * (x.c1hi / 8 % 512) + 4096 * (x.c1hi / 4096) by
          simp only [RowInput.carryC1, RowInput.c1hi, RowInput.sumC1, RowInput.d1hi]; omega))
      (by result)
  · exact xor_at (x.xd2) (x.a2lo % 256) (fun _ => xor8_contains xd2 (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.xd3) (x.a2lo / 256) (fun _ => xor8_contains xd3 (by simp only [RowInput.a2lo]; omega)) (by direct)
      (by quotient (-7864320) (show x.a.lo + x.b.lo + x.mx.lo + x.my.lo + x.xb2 + 16 * x.xb3 + 128 * x.xb4 =
        65536 * (x.carryA0 % 2) + 131072 * (x.carryA0 / 2) + 65536 * (x.carryA2 % 2) +
          131072 * (x.carryA2 / 2) + x.a2lo % 256 + 256 * (x.a2lo / 256) by
          simp only [RowInput.carryA0, RowInput.a1lo, RowInput.sumA0, RowInput.carryA2, RowInput.a2lo,
            RowInput.sumA2, RowInput.b1lo]; omega))
      (by result)
  · exact xor_at (x.xd0) (x.a2hi % 256) (fun _ => xor8_contains xd0 (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.xd1) (x.a2hi / 256) (fun _ => xor8_contains xd1 (by simp only [RowInput.a2hi]; omega)) (by direct)
      (by quotient (-7864320) (show x.a.hi + x.b.hi + x.mx.hi + x.my.hi + x.carryA0 % 2 + 2 * (x.carryA0 / 2) +
        x.xb5 + 16 * x.xb0 + 128 * x.xb1 + x.carryA2 % 2 + 2 * (x.carryA2 / 2) =
        65536 * (x.carryA1 % 2) + 131072 * (x.carryA1 / 2) + 65536 * (x.carryA3 % 2) +
          131072 * (x.carryA3 / 2) + x.a2hi % 256 + 256 * (x.a2hi / 256) by
          simp only [RowInput.carryA1, RowInput.a1hi, RowInput.sumA1, RowInput.carryA3, RowInput.a2hi,
            RowInput.sumA3, RowInput.b1hi]; omega))
      (by result)
  · exact xor_at (x.xb2 + 16 * x.xb3) (x.c2lo % 128) (fun _ => xor7_contains (by omega) (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.xb4) (x.c2lo / 128) (fun _ => xor9_contains xb4 (by simp only [RowInput.c2lo]; omega)) (by direct)
      (by quotient 1997537281 (show x.c.lo + x.xd2 + 256 * x.xd3 + x.xe1 + 256 * x.xe2 = 65536 * x.carryC0 +
        65536 * x.carryC2 + x.c2lo % 128 + 128 * (x.c2lo / 128) by
          simp only [RowInput.carryC0, RowInput.c1lo, RowInput.sumC0, RowInput.d1lo, RowInput.carryC2,
            RowInput.c2lo, RowInput.sumC2, RowInput.d2lo]; omega))
      (by result)
  · exact xor_at (16 * x.xb0 + x.xb5) (x.c2hi % 128) (fun _ => xor7_contains (by omega) (by omega)) (by direct) (by direct) (by result)
  · exact xor_at (x.xb1) (x.c2hi / 128) (fun _ => xor9_contains xb1 (by simp only [RowInput.c2hi]; omega)) (by direct)
      (by quotient 1997537281 (show x.c.hi + x.xd0 + 256 * x.xd1 + x.carryC0 + x.xe3 + 256 * x.xe0 + x.carryC2 =
        65536 * x.carryC1 + 65536 * x.carryC3 + x.c2hi % 128 + 128 * (x.c2hi / 128) by
          simp only [RowInput.carryC1, RowInput.c1hi, RowInput.sumC1, RowInput.d1hi, RowInput.carryC3,
            RowInput.c2hi, RowInput.sumC3, RowInput.d2hi]; omega))
      (by result)

end Airbender.NonVacuous.Blake2GSpan
