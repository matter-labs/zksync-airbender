module
public import Proven.NonVacuous.KeccakSplitSpan.Parity.Honest
public import Proven.NonVacuous.KeccakSplitSpan.Parity.Tables
public import Proven.NonVacuous.SpanTactics
public import Proven.KeccakSplit.ColumnParity.OpIndex

@[expose] public section

/-! The 23 imported lookups of a column-parity row hold for the honest assignment of valid inputs, over BabyBear:
    the pointer alignment, the slot and control queries of the call, the four iota queries and the sixteen
    five-nibble XOR queries, each at the setup row of its keys (`Tables.lean`). -/

namespace Airbender.NonVacuous.KeccakSplitSpan.Parity
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- An entry whose evaluation is the honest value. -/
local macro "direct" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column, RowInput.control, round]
  try push_cast
  try ring))

/-- An XOR result entry: the honest column is the XOR by definition. -/
local macro "result" : tactic => `(tactic| (
  simp only [Expression.eval, Verification.environment, honest_column]
  push_cast
  simp only [zero_add, one_mul]
  rfl))

variable {p : Nat} [Fact p.Prime]

theorem rcByte_lt (b : Nat) : rcByte b < 256 := Nat.mod_lt _ (by decide)

theorem byte_xor_lt {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) ha hb

theorem out_lt {x : RowInput} (valid : x.Valid) (kind : kindAt x.call = .columnParity) (m : Nat) :
    out x m < 65536 := by
  have lane (m : Nat) := valid.limb (l := 0) (by rw [kind]; decide) m
  have b0 := byte_xor_lt (Nat.mod_lt (x.limb 0 0) (by decide)) (rcByte_lt (round x))
  have b1 := byte_xor_lt (by have := lane 0; omega : x.limb 0 0 / 256 < 256) (rcByte_lt (round x + 32))
  have b2 := byte_xor_lt (by have := lane 1; omega : x.limb 0 1 / 256 < 256) (rcByte_lt (round x + 96))
  have b3 := byte_xor_lt (by have := lane 3; omega : x.limb 0 3 / 256 < 256) (rcByte_lt (round x + 224))
  have l2 := lane 2
  unfold out
  split <;> omega

theorem parity_lt (x : RowInput) (m : Nat) : parity x m < 65536 := by
  have nibble (j : Nat) : parityNib x m j < 16 :=
    Nat.xor_lt_two_pow (n := 4) (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (nib_lt _ _)
      (nib_lt _ _)) (nib_lt _ _)) (nib_lt _ _)) (nib_lt _ _)
  have n0 := nibble 0
  have n1 := nibble 1
  have n2 := nibble 2
  have n3 := nibble 3
  unfold parity
  omega

theorem round_le {x : RowInput} (valid : x.Valid) : round x ≤ 24 := by
  have call := valid.call
  unfold round
  split <;> omega

theorem lookups (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .columnParity) (hp : p = 2013265921) :
    ∀ i (h : i < (FlatOperation.lookups (ColumnParity.importedConstraints (ColumnParity.setup (p := p)))).length),
      ((FlatOperation.lookups (ColumnParity.importedConstraints (ColumnParity.setup (p := p)))).get ⟨i, h⟩).Contains
        (Verification.environment (assignment x)) := by
  subst hp
  have lane (l : Nat) (m : Nat) (small : l < 6 := by decide) := valid.limb (l := l) (by rw [kind]; exact small) m
  have pointer := valid.pointer
  simp only [Word.Bounded, limbBase] at pointer
  have round := round_le valid
  have out0 := out_lt valid kind 0
  have out1 := out_lt valid kind 1
  have out3 := out_lt valid kind 3
  have l00 := lane 0 0
  have l01 := lane 0 1
  have l03 := lane 0 3
  have b0 := byte_xor_lt (Nat.mod_lt (x.limb 0 0) (by decide)) (rcByte_lt (Parity.round x))
  have b1 := byte_xor_lt (by omega : x.limb 0 0 / 256 < 256) (rcByte_lt (Parity.round x + 32))
  have b2 := byte_xor_lt (by omega : x.limb 0 1 / 256 < 256) (rcByte_lt (Parity.round x + 96))
  have b3 := byte_xor_lt (by omega : x.limb 0 3 / 256 < 256) (rcByte_lt (Parity.round x + 224))
  intro i h
  have size : i < 23 := by
    have count : (FlatOperation.lookups (ColumnParity.importedConstraints
      (ColumnParity.setup (p := 2013265921)))).length = 23 := by rfl
    omega
  interval_cases i <;> op_index
  · refine range_of_eval (n := (x.read 1).lo / 256) ?_ (by simp only [Trace.timestampBase]; omega) (by decide)
    quotient (-7864320) (show (x.read 1).lo = 256 * ((x.read 1).lo / 256) by omega)
  · exact slots_at valid.call kind (by direct) (by direct) (by direct) (by direct) (by direct) (by direct)
      (by direct) (by direct)
  · exact control_at valid.call kind (by direct) (by direct) (by direct) (by direct) (by direct) (by direct)
      (by direct) (by direct)
  · exact iota_at (a := x.limb 0 0 % 256) (b := Parity.round x) (by omega) (by omega) (by direct) (by direct)
      (by cast_identity 2013265921 (show nib (out x 0) 0 + 16 * nib (out x 0) 1 =
        (x.limb 0 0 % 256 ^^^ rcByte (Parity.round x)) by simp only [out, nib, Nat.reducePow]; omega))
      (by direct) (by direct) (by direct) (by direct) (by direct)
  · exact iota_at (a := x.limb 0 0 / 256) (b := Parity.round x + 32) (by omega) (by omega)
      (by quotient (-7864320) (show x.limb 0 0 = x.limb 0 0 % 256 + 256 * (x.limb 0 0 / 256) by omega))
      (by direct)
      (by quotient (-7864320) (show out x 0 = nib (out x 0) 0 + 16 * nib (out x 0) 1 +
        256 * (x.limb 0 0 / 256 ^^^ rcByte (Parity.round x + 32)) by simp only [out, nib, Nat.reducePow]; omega))
      (by direct) (by direct) (by direct) (by direct) (by direct)
  · exact iota_at (a := x.limb 0 1 / 256) (b := Parity.round x + 96) (by omega) (by omega)
      (by quotient (-7864320) (show x.limb 0 1 = x.limb 0 1 % 256 + 256 * (x.limb 0 1 / 256) by omega))
      (by direct)
      (by quotient (-7864320) (show out x 1 = nib (out x 1) 0 + 16 * nib (out x 1) 1 +
        256 * (x.limb 0 1 / 256 ^^^ rcByte (Parity.round x + 96)) by simp only [out, nib, Nat.reducePow]; omega))
      (by direct) (by direct) (by direct) (by direct) (by direct)
  · exact iota_at (a := x.limb 0 3 / 256) (b := Parity.round x + 224) (by omega) (by omega)
      (by quotient (-7864320) (show x.limb 0 3 = x.limb 0 3 % 256 + 256 * (x.limb 0 3 / 256) by omega))
      (by direct)
      (by quotient (-7864320) (show out x 3 = nib (out x 3) 0 + 16 * nib (out x 3) 1 +
        256 * (x.limb 0 3 / 256 ^^^ rcByte (Parity.round x + 224)) by simp only [out, nib, Nat.reducePow]; omega))
      (by direct) (by direct) (by direct) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 0) 0) (a1 := nib (x.limb 1 0) 0) (a2 := nib (x.limb 2 0) 0)
      (a3 := nib (x.limb 3 0) 0) (a4 := nib (x.limb 4 0) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 0) 1) (a1 := nib (x.limb 1 0) 1) (a2 := nib (x.limb 2 0) 1)
      (a3 := nib (x.limb 3 0) 1) (a4 := nib (x.limb 4 0) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 0) 2) (a1 := nib (x.limb 1 0) 2) (a2 := nib (x.limb 2 0) 2)
      (a3 := nib (x.limb 3 0) 2) (a4 := nib (x.limb 4 0) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 0) 3) (a1 := nib (x.limb 1 0) 3) (a2 := nib (x.limb 2 0) 3)
      (a3 := nib (x.limb 3 0) 3) (a4 := nib (x.limb 4 0) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (out_lt valid kind 0)).1)
      (by quotient (-491520) (nib_limb (lane 1 0)).1)
      (by quotient (-491520) (nib_limb (lane 2 0)).1)
      (by quotient (-491520) (nib_limb (lane 3 0)).1)
      (by quotient (-491520) (nib_limb (lane 4 0)).1)
      (by quotient (-491520) (show parity x 0 = parityNib x 0 0 + 16 * parityNib x 0 1 + 256 * parityNib x 0 2 +
        4096 * (nib (out x 0) 3 ^^^ nib (x.limb 1 0) 3 ^^^ nib (x.limb 2 0) 3 ^^^ nib (x.limb 3 0) 3 ^^^
          nib (x.limb 4 0) 3) from rfl))
      (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 1) 0) (a1 := nib (x.limb 1 1) 0) (a2 := nib (x.limb 2 1) 0)
      (a3 := nib (x.limb 3 1) 0) (a4 := nib (x.limb 4 1) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 1) 1) (a1 := nib (x.limb 1 1) 1) (a2 := nib (x.limb 2 1) 1)
      (a3 := nib (x.limb 3 1) 1) (a4 := nib (x.limb 4 1) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 1) 2) (a1 := nib (x.limb 1 1) 2) (a2 := nib (x.limb 2 1) 2)
      (a3 := nib (x.limb 3 1) 2) (a4 := nib (x.limb 4 1) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 1) 3) (a1 := nib (x.limb 1 1) 3) (a2 := nib (x.limb 2 1) 3)
      (a3 := nib (x.limb 3 1) 3) (a4 := nib (x.limb 4 1) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (out_lt valid kind 1)).1)
      (by quotient (-491520) (nib_limb (lane 1 1)).1)
      (by quotient (-491520) (nib_limb (lane 2 1)).1)
      (by quotient (-491520) (nib_limb (lane 3 1)).1)
      (by quotient (-491520) (nib_limb (lane 4 1)).1)
      (by quotient (-491520) (show parity x 1 = parityNib x 1 0 + 16 * parityNib x 1 1 + 256 * parityNib x 1 2 +
        4096 * (nib (out x 1) 3 ^^^ nib (x.limb 1 1) 3 ^^^ nib (x.limb 2 1) 3 ^^^ nib (x.limb 3 1) 3 ^^^
          nib (x.limb 4 1) 3) from rfl))
      (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 2) 0) (a1 := nib (x.limb 1 2) 0) (a2 := nib (x.limb 2 2) 0)
      (a3 := nib (x.limb 3 2) 0) (a4 := nib (x.limb 4 2) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 2) 1) (a1 := nib (x.limb 1 2) 1) (a2 := nib (x.limb 2 2) 1)
      (a3 := nib (x.limb 3 2) 1) (a4 := nib (x.limb 4 2) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 2) 2) (a1 := nib (x.limb 1 2) 2) (a2 := nib (x.limb 2 2) 2)
      (a3 := nib (x.limb 3 2) 2) (a4 := nib (x.limb 4 2) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 2) 3) (a1 := nib (x.limb 1 2) 3) (a2 := nib (x.limb 2 2) 3)
      (a3 := nib (x.limb 3 2) 3) (a4 := nib (x.limb 4 2) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (out_lt valid kind 2)).1)
      (by quotient (-491520) (nib_limb (lane 1 2)).1)
      (by quotient (-491520) (nib_limb (lane 2 2)).1)
      (by quotient (-491520) (nib_limb (lane 3 2)).1)
      (by quotient (-491520) (nib_limb (lane 4 2)).1)
      (by quotient (-491520) (show parity x 2 = parityNib x 2 0 + 16 * parityNib x 2 1 + 256 * parityNib x 2 2 +
        4096 * (nib (out x 2) 3 ^^^ nib (x.limb 1 2) 3 ^^^ nib (x.limb 2 2) 3 ^^^ nib (x.limb 3 2) 3 ^^^
          nib (x.limb 4 2) 3) from rfl))
      (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 3) 0) (a1 := nib (x.limb 1 3) 0) (a2 := nib (x.limb 2 3) 0)
      (a3 := nib (x.limb 3 3) 0) (a4 := nib (x.limb 4 3) 0)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 3) 1) (a1 := nib (x.limb 1 3) 1) (a2 := nib (x.limb 2 3) 1)
      (a3 := nib (x.limb 3 3) 1) (a4 := nib (x.limb 4 3) 1)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 3) 2) (a1 := nib (x.limb 1 3) 2) (a2 := nib (x.limb 2 3) 2)
      (a3 := nib (x.limb 3 3) 2) (a4 := nib (x.limb 4 3) 2)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by direct) (by direct) (by direct) (by direct) (by direct) (by result) (by direct) (by direct)
  · exact xor5_at (a0 := nib (out x 3) 3) (a1 := nib (x.limb 1 3) 3) (a2 := nib (x.limb 2 3) 3)
      (a3 := nib (x.limb 3 3) 3) (a4 := nib (x.limb 4 3) 3)
      (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _) (nib_lt _ _)
      (by quotient (-491520) (nib_limb (out_lt valid kind 3)).1)
      (by quotient (-491520) (nib_limb (lane 1 3)).1)
      (by quotient (-491520) (nib_limb (lane 2 3)).1)
      (by quotient (-491520) (nib_limb (lane 3 3)).1)
      (by quotient (-491520) (nib_limb (lane 4 3)).1)
      (by quotient (-491520) (show parity x 3 = parityNib x 3 0 + 16 * parityNib x 3 1 + 256 * parityNib x 3 2 +
        4096 * (nib (out x 3) 3 ^^^ nib (x.limb 1 3) 3 ^^^ nib (x.limb 2 3) 3 ^^^ nib (x.limb 3 3) 3 ^^^
          nib (x.limb 4 3) 3) from rfl))
      (by direct) (by direct)

end Airbender.NonVacuous.KeccakSplitSpan.Parity
