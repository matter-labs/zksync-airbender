module
public import Proven.NonVacuous.KeccakSplitSpan.Tables
public import Proven.KeccakSplit.Setup.ColumnParity.Rows
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Membership of honest queries in the exported column-parity setup (`ColumnParity.setup`): an iota query at its
    two keys, the slot and control queries of a parity call at the call's controller row, and a five-nibble XOR
    query at its nibbles. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Parity
open Keccak.Split Keccak.Split.SetupProofs Keccak.Split.ColumnParity.SetupProofs

variable {p : Nat} [Fact p.Prime] {env : Environment (ZMod p)}

/-- A query of the column-parity setup whose entries evaluate to formula row `n`. -/
theorem formula_contains {entry : Vector (Expression (ZMod p)) 8} (n : Nat) (bound : n < 4194304)
    {row : Vector Nat 8} (formula : formulaRow n = row)
    (values : ∀ j : Fin 8, entry[j].eval env = ((row[j] : Nat) : ZMod p)) :
    (Lookup.mk (ColumnParity.setup (p := p)).toRaw entry).Contains env :=
  setup_contains traceLen_eq setupRow_eq n bound (formula ▸ values)

/-- The iota query (tag 38): byte `a`, key `b`, `a ^ rcByte b`. -/
theorem iota_at {e0 e1 e2 e3 e4 e5 e6 e7 : Expression (ZMod p)} {a b : Nat} (ha : a < 256) (hb : b < 256)
    (v0 : e0.eval env = (a : ZMod p)) (v1 : e1.eval env = (b : ZMod p))
    (v2 : e2.eval env = ((a ^^^ rcByte b : Nat) : ZMod p)) (v3 : e3.eval env = 0) (v4 : e4.eval env = 0)
    (v5 : e5.eval env = 0) (v6 : e6.eval env = 0) (v7 : e7.eval env = 38) :
    (Lookup.mk (ColumnParity.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7]).Contains env := by
  refine formula_contains (a + 256 * b) (by omega) (row := #v[a, b, a ^^^ rcByte b, 0, 0, 0, 0, 38]) ?_ ?_
  · have low : (a + 256 * b) % 256 = a := by omega
    have high : (a + 256 * b) / 256 = b := by omega
    simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, ite_eq_left, low,
      high]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]

/-- The five-nibble XOR query (tag 64). -/
theorem xor5_at {e0 e1 e2 e3 e4 e5 e6 e7 : Expression (ZMod p)} {a0 a1 a2 a3 a4 : Nat} (h0 : a0 < 16)
    (h1 : a1 < 16) (h2 : a2 < 16) (h3 : a3 < 16) (h4 : a4 < 16)
    (v0 : e0.eval env = (a0 : ZMod p)) (v1 : e1.eval env = (a1 : ZMod p)) (v2 : e2.eval env = (a2 : ZMod p))
    (v3 : e3.eval env = (a3 : ZMod p)) (v4 : e4.eval env = (a4 : ZMod p))
    (v5 : e5.eval env = ((a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 : Nat) : ZMod p)) (v6 : e6.eval env = 0)
    (v7 : e7.eval env = 64) :
    (Lookup.mk (ColumnParity.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7]).Contains env := by
  refine formula_contains (65780 + (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4)) (by omega)
    (row := #v[a0, a1, a2, a3, a4, a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4, 0, 64]) ?_ ?_
  · obtain ⟨n0, n1, n2, n3, n4⟩ := nib_pack h0 h1 h2 h3 h4
    have offset : 65780 + (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) - 65780 =
        a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4 := by omega
    simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, ite_eq_left,
      ite_eq_right, offset, n0, n1, n2, n3, n4]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]

/-- A parity call's row in a controller region at `base` (slots 65536, control 65658). -/
theorem ctl_call {k base : Nat} (call : k < 361) (kind : kindAt k = .columnParity) :
    ColumnParity.SetupProofs.callAt (base + ctlRow 0 k - base) = k ∧ 1 ≤ ctlRow 0 k ∧ ctlRow 0 k ≤ 121 := by
  have small : k % 15 < 5 := by
    unfold kindAt at kind
    split_ifs at kind <;> omega
  refine ⟨?_, by unfold ctlRow; omega, by unfold ctlRow; omega⟩
  rw [Nat.add_sub_cancel_left]
  exact callIndex_ctlRow (Nat.zero_le _) small

/-- The slot query (tag 62) of parity call `k`. -/
theorem slots_at {e0 e1 e2 e3 e4 e5 e6 e7 : Expression (ZMod p)} {k : Nat} (call : k < 361)
    (kind : kindAt k = .columnParity)
    (v0 : e0.eval env = ((controlAt k + 2048 : Nat) : ZMod p)) (v1 : e1.eval env = (slotNat k 0 : ZMod p))
    (v2 : e2.eval env = (slotNat k 1 : ZMod p)) (v3 : e3.eval env = (slotNat k 2 : ZMod p))
    (v4 : e4.eval env = (slotNat k 3 : ZMod p)) (v5 : e5.eval env = (slotNat k 4 : ZMod p))
    (v6 : e6.eval env = (slotNat k 5 : ZMod p)) (v7 : e7.eval env = 62) :
    (Lookup.mk (ColumnParity.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7]).Contains env := by
  obtain ⟨index, low, high⟩ := ctl_call (base := 65536) call kind
  refine formula_contains (65536 + ctlRow 0 k) (by omega) (row := #v[controlAt k + 2048, slotNat k 0,
    slotNat k 1, slotNat k 2, slotNat k 3, slotNat k 4, slotNat k 5, 62]) ?_ ?_
  · simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, ite_eq_left,
      ite_eq_right, index]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]

/-- The control query (tag 63) of parity call `k`: control, execute, next control, iota round. -/
theorem control_at {e0 e1 e2 e3 e4 e5 e6 e7 : Expression (ZMod p)} {k : Nat} (call : k < 361)
    (kind : kindAt k = .columnParity)
    (v0 : e0.eval env = (controlAt k : ZMod p)) (v1 : e1.eval env = 1)
    (v2 : e2.eval env = (bump (controlAt k) : ZMod p))
    (v3 : e3.eval env = ((if k % 5 = 0 then k / 15 else 0 : Nat) : ZMod p)) (v4 : e4.eval env = 0)
    (v5 : e5.eval env = 0) (v6 : e6.eval env = 0) (v7 : e7.eval env = 63) :
    (Lookup.mk (ColumnParity.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7]).Contains env := by
  obtain ⟨index, low, high⟩ := ctl_call (base := 65658) call kind
  refine formula_contains (65658 + ctlRow 0 k) (by omega) (row := #v[controlAt k, 1, bump (controlAt k),
    if k % 5 = 0 then k / 15 else 0, 0, 0, 0, 63]) ?_ ?_
  · simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, ite_eq_left,
      ite_eq_right, index]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7]

end Airbender.NonVacuous.KeccakSplitSpan.Parity
