module
public import Slop.NonVacuous.KeccakSplitSpan.Parity.Tables
public import Slop.KeccakSplit.Setup.Chi5.Rows

@[expose] public section

/-! Membership of honest queries in the exported chi setup (`Chi5.setup`): a chi query at its five input nibbles,
    and the control query of a chi call at the call's controller row. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Chi
open Keccak.Split Keccak.Split.SetupProofs Keccak.Split.Chi5.SetupProofs

variable {p : Nat} [Fact p.Prime] {env : Environment (ZMod p)}

/-- A query of the chi setup whose entries evaluate to formula row `n`. -/
theorem formula_contains {entry : Vector (Expression (ZMod p)) 11} (n : Nat) (bound : n < 4194304)
    {row : Vector Nat 11} (formula : formulaRow n = row)
    (values : ∀ j : Fin 11, entry[j].eval env = ((row[j] : Nat) : ZMod p)) :
    (Lookup.mk (Chi5.setup (p := p)).toRaw entry).Contains env :=
  setup_contains traceLen_eq setupRow_eq n bound (formula ▸ values)

/-- Chi on four bits of lane `a` with its two neighbours `b`, `c`. -/
abbrev chi4 (a b c : Nat) : Nat := a ^^^ ((15 ^^^ b) &&& c)

/-- The chi query (tag 65): five input nibbles and their chi. -/
theorem chi_at {e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Expression (ZMod p)} {a0 a1 a2 a3 a4 : Nat} (h0 : a0 < 16)
    (h1 : a1 < 16) (h2 : a2 < 16) (h3 : a3 < 16) (h4 : a4 < 16)
    (v0 : e0.eval env = (a0 : ZMod p)) (v1 : e1.eval env = (a1 : ZMod p)) (v2 : e2.eval env = (a2 : ZMod p))
    (v3 : e3.eval env = (a3 : ZMod p)) (v4 : e4.eval env = (a4 : ZMod p))
    (v5 : e5.eval env = ((chi4 a0 a1 a2 : Nat) : ZMod p)) (v6 : e6.eval env = ((chi4 a1 a2 a3 : Nat) : ZMod p))
    (v7 : e7.eval env = ((chi4 a2 a3 a4 : Nat) : ZMod p)) (v8 : e8.eval env = ((chi4 a3 a4 a0 : Nat) : ZMod p))
    (v9 : e9.eval env = ((chi4 a4 a0 a1 : Nat) : ZMod p)) (v10 : e10.eval env = 65) :
    (Lookup.mk (Chi5.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]).Contains env := by
  refine formula_contains (a0 + 16 * a1 + 256 * a2 + 4096 * a3 + 65536 * a4) (by omega)
    (row := #v[a0, a1, a2, a3, a4, chi4 a0 a1 a2, chi4 a1 a2 a3, chi4 a2 a3 a4, chi4 a3 a4 a0, chi4 a4 a0 a1, 65])
    ?_ ?_
  · obtain ⟨n0, n1, n2, n3, n4⟩ := Parity.nib_pack h0 h1 h2 h3 h4
    simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8, spec9,
      spec10, chiOut, ite_eq_left, n0, n1, n2, n3, n4, Nat.reduceAdd, Nat.reduceMod]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]

/-- The control query (tag 66) of chi call `k`: control, execute, next control, five slots, plane. -/
theorem control_at {e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Expression (ZMod p)} {k : Nat} (call : k < 361)
    (kind : kindAt k = .chi5) (v0 : e0.eval env = (controlAt k : ZMod p)) (v1 : e1.eval env = 1)
    (v2 : e2.eval env = (bump (controlAt k) : ZMod p)) (v3 : e3.eval env = (slotNat k 0 : ZMod p))
    (v4 : e4.eval env = (slotNat k 1 : ZMod p)) (v5 : e5.eval env = (slotNat k 2 : ZMod p))
    (v6 : e6.eval env = (slotNat k 3 : ZMod p)) (v7 : e7.eval env = (slotNat k 4 : ZMod p))
    (v8 : e8.eval env = ((k % 5 : Nat) : ZMod p)) (v9 : e9.eval env = 0) (v10 : e10.eval env = 66) :
    (Lookup.mk (Chi5.setup (p := p)).toRaw #v[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]).Contains env := by
  have late : 10 ≤ k % 15 ∧ k % 15 < 15 := by
    unfold kindAt at kind
    split_ifs at kind
    omega
  have index : Chi5.SetupProofs.callAt (1048576 + ctlRow 10 k - 1048576) = k := by
    rw [Nat.add_sub_cancel_left]
    exact callIndex_ctlRow late.1 late.2
  have small : 1 ≤ ctlRow 10 k ∧ ctlRow 10 k ≤ 120 := by unfold ctlRow; omega
  refine formula_contains (1048576 + ctlRow 10 k) (by omega) (row := #v[controlAt k, 1, bump (controlAt k),
    slotNat k 0, slotNat k 1, slotNat k 2, slotNat k 3, slotNat k 4, k % 5, 0, 66]) ?_ ?_
  · simp (disch := omega) only [formulaRow, spec0, spec1, spec2, spec3, spec4, spec5, spec6, spec7, spec8, spec9,
      spec10, ite_eq_left, ite_eq_right, ctl, index]
  · intro j
    fin_cases j <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]

end Airbender.NonVacuous.KeccakSplitSpan.Chi
