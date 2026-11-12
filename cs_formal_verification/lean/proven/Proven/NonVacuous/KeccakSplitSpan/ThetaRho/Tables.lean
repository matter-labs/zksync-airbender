module
public import Proven.NonVacuous.KeccakSplitSpan.Tables
public import Proven.KeccakSplit.Setup.ThetaRho.Rows
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Membership of honest queries in the exported theta+rho setup (`ThetaRho.setup`): a byte XOR query at its two
    bytes, an XOR-and-split query at its byte, `D` byte and shift, and the control and slot queries of a theta+rho
    call at the call's controller row. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Keccak.Split Keccak.Split.SetupProofs Keccak.Split.ThetaRho.SetupProofs

variable {p : Nat} [Fact p.Prime] {env : Environment (ZMod p)}

/-- A query of the theta+rho setup whose entries evaluate to formula row `n`. -/
theorem formula_contains {entry : Vector (Expression (ZMod p)) 9} (n : Nat) (bound : n < 4194304)
    {row : Vector Nat 9} (formula : formulaRow n = row)
    (values : ∀ j : Fin 9, entry[j].eval env = ((row[j] : Nat) : ZMod p)) :
    (Lookup.mk (ThetaRho.setup (p := p)).toRaw entry).Contains env :=
  setup_contains traceLen_eq setupRow_eq n bound (formula ▸ values)

/-- The byte XOR query (tag 4). -/
theorem byte_xor_at {e0 e1 e2 e3 e4 e5 e6 e7 e8 : Expression (ZMod p)} {a b : Nat} (ha : a < 256)
    (hb : b < 256) (v0 : e0.eval env = (a : ZMod p)) (v1 : e1.eval env = (b : ZMod p))
    (v2 : e2.eval env = ((a ^^^ b : Nat) : ZMod p)) (v3 : e3.eval env = 0) (v4 : e4.eval env = 0)
    (v5 : e5.eval env = 0) (v6 : e6.eval env = 0) (v7 : e7.eval env = 0) (v8 : e8.eval env = 4) :
    (Lookup.mk (ThetaRho.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, e8]).Contains env := by
  refine formula_contains (256 * a + b) (by omega) (row := #v[a, b, a ^^^ b, 0, 0, 0, 0, 0, 4]) ?_ ?_
  · have high : (256 * a + b) / 256 = a := by omega
    have low : (256 * a + b) % 256 = b := by omega
    simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8,
      ite_eq_left, high, low]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]

/-- The XOR-and-split query (tag 58): byte `a`, byte `b`, shift `s`, then `(a ^ b) << s` and its overflow. -/
theorem split_at {e0 e1 e2 e3 e4 e5 e6 e7 e8 : Expression (ZMod p)} {a b s : Nat} (ha : a < 256)
    (hb : b < 256) (hs : s < 8) (v0 : e0.eval env = (a : ZMod p)) (v1 : e1.eval env = (b : ZMod p))
    (v2 : e2.eval env = (s : ZMod p)) (v3 : e3.eval env = (((a ^^^ b) * 2 ^ s % 256 : Nat) : ZMod p))
    (v4 : e4.eval env = (((a ^^^ b) / 2 ^ (8 - s) : Nat) : ZMod p)) (v5 : e5.eval env = 0)
    (v6 : e6.eval env = 0) (v7 : e7.eval env = 0) (v8 : e8.eval env = 58) :
    (Lookup.mk (ThetaRho.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, e8]).Contains env := by
  refine formula_contains (65536 + (a + 256 * b + 65536 * s)) (by omega)
    (row := #v[a, b, s, (a ^^^ b) * 2 ^ s % 256, (a ^^^ b) / 2 ^ (8 - s), 0, 0, 0, 58]) ?_ ?_
  · have ka : (65536 + (a + 256 * b + 65536 * s) - 65536) % 256 = a := by omega
    have kb : (65536 + (a + 256 * b + 65536 * s) - 65536) / 256 % 256 = b := by omega
    have ks : (65536 + (a + 256 * b + 65536 * s) - 65536) / 65536 = s := by omega
    simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8,
      ite_eq_left, ite_eq_right, splitA, splitB, splitS, ka, kb, ks]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]

/-- A theta+rho call's row in a controller region at `base` (control 589824, slots 589945). -/
theorem ctl_call {k base : Nat} (call : k < 361) (kind : kindAt k = .thetaRho) :
    ThetaRho.SetupProofs.callAt (base + ctlRow 5 k - base) = k ∧ 1 ≤ ctlRow 5 k ∧ ctlRow 5 k ≤ 120 := by
  have middle : 5 ≤ k % 15 ∧ k % 15 < 10 := by
    unfold kindAt at kind
    split_ifs at kind
    omega
  refine ⟨?_, by unfold ctlRow; omega, by unfold ctlRow; omega⟩
  rw [Nat.add_sub_cancel_left]
  exact callIndex_ctlRow middle.1 middle.2

/-- The control query (tag 59) of theta+rho call `k`: control, execute, next control, the one-hot column flags. -/
theorem control_at {e0 e1 e2 e3 e4 e5 e6 e7 e8 : Expression (ZMod p)} {k : Nat} (call : k < 361)
    (kind : kindAt k = .thetaRho) (v0 : e0.eval env = (controlAt k : ZMod p)) (v1 : e1.eval env = 1)
    (v2 : e2.eval env = (bump (controlAt k) : ZMod p))
    (v3 : e3.eval env = ((if k % 5 = 0 then 1 else 0 : Nat) : ZMod p))
    (v4 : e4.eval env = ((if k % 5 = 1 then 1 else 0 : Nat) : ZMod p))
    (v5 : e5.eval env = ((if k % 5 = 2 then 1 else 0 : Nat) : ZMod p))
    (v6 : e6.eval env = ((if k % 5 = 3 then 1 else 0 : Nat) : ZMod p))
    (v7 : e7.eval env = ((if k % 5 = 4 then 1 else 0 : Nat) : ZMod p)) (v8 : e8.eval env = 59) :
    (Lookup.mk (ThetaRho.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, e8]).Contains env := by
  obtain ⟨index, low, high⟩ := ctl_call (base := 589824) call kind
  refine formula_contains (589824 + ctlRow 5 k) (by omega) (row := #v[controlAt k, 1, bump (controlAt k),
    if k % 5 = 0 then 1 else 0, if k % 5 = 1 then 1 else 0, if k % 5 = 2 then 1 else 0,
    if k % 5 = 3 then 1 else 0, if k % 5 = 4 then 1 else 0, 59]) ?_ ?_
  · simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8,
      ite_eq_left, ite_eq_right, ctl, flag, index]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]

/-- The slot query (tag 60) of theta+rho call `k`. -/
theorem slots_at {e0 e1 e2 e3 e4 e5 e6 e7 e8 : Expression (ZMod p)} {k : Nat} (call : k < 361)
    (kind : kindAt k = .thetaRho)
    (v0 : e0.eval env = ((controlAt k + 2048 : Nat) : ZMod p)) (v1 : e1.eval env = (slotNat k 0 : ZMod p))
    (v2 : e2.eval env = (slotNat k 1 : ZMod p)) (v3 : e3.eval env = (slotNat k 2 : ZMod p))
    (v4 : e4.eval env = (slotNat k 3 : ZMod p)) (v5 : e5.eval env = (slotNat k 4 : ZMod p))
    (v6 : e6.eval env = (slotNat k 5 : ZMod p)) (v7 : e7.eval env = (slotNat k 6 : ZMod p))
    (v8 : e8.eval env = 60) :
    (Lookup.mk (ThetaRho.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, e8]).Contains env := by
  obtain ⟨index, low, high⟩ := ctl_call (base := 589945) call kind
  refine formula_contains (589945 + ctlRow 5 k) (by omega) (row := #v[controlAt k + 2048, slotNat k 0,
    slotNat k 1, slotNat k 2, slotNat k 3, slotNat k 4, slotNat k 5, slotNat k 6, 60]) ?_ ?_
  · simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8,
      ite_eq_left, ite_eq_right, slt, index]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8]

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
