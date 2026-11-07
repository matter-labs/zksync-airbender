import Human.ISA.Delegations
import Human.Circuits.Bigint.Word
import Slop.Arithmetic.Digits

/-! The spec side of the bigint delegate link (`RV.Delegation.bigint`): 256-bit numbers as eight words and as sixteen
    16-bit limbs, and the control byte of `x12`. State-free. -/

namespace Airbender.Bigint.Proofs
open Arithmetic
set_option warningAsError true

theorem value_lt {limbs : Vector Nat 16} (bounded : ∀ i : Fin 16, limbs[i] < 65536) : value limbs < 2 ^ 256 := by
  have bound := weighted_limb_bound (length := 16) (radix := 65536) (by decide) (limbs := fun i => limbs[i]) bounded
  simpa only [value, limbBase] using bound.trans_eq (by norm_num)

private theorem value_expand (l : Vector Nat 16) :
    value l = l[0] + 65536 * l[1] + 65536 ^ 2 * l[2] + 65536 ^ 3 * l[3] + 65536 ^ 4 * l[4] +
      65536 ^ 5 * l[5] + 65536 ^ 6 * l[6] + 65536 ^ 7 * l[7] + 65536 ^ 8 * l[8] + 65536 ^ 9 * l[9] +
      65536 ^ 10 * l[10] + 65536 ^ 11 * l[11] + 65536 ^ 12 * l[12] + 65536 ^ 13 * l[13] +
      65536 ^ 14 * l[14] + 65536 ^ 15 * l[15] := by
  simp only [value, limbBase, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.val_zero, Fin.val_succ, Fin.getElem_fin]
  ring

/-- Eight words whose halves are the sixteen limbs encode the limbs' value. -/
theorem toU256_of_limbs (ws : Vector RV.Word 8) (l : Vector Nat 16)
    (words : ∀ i : Fin 8, ws[i].toNat = l[2 * i.val] + 65536 * l[2 * i.val + 1]) :
    RV.Delegation.toU256 ws = value l := by
  have w0 := words 0
  have w1 := words 1
  have w2 := words 2
  have w3 := words 3
  have w4 := words 4
  have w5 := words 5
  have w6 := words 6
  have w7 := words 7
  simp only [Fin.getElem_fin, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at w0 w1 w2 w3 w4 w5 w6 w7
  rw [value_expand]
  simp only [RV.Delegation.toU256, show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldr,
    Fin.getElem_fin]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at *
  norm_num at w0 w1 w2 w3 w4 w5 w6 w7 ⊢
  rw [w0, w1, w2, w3, w4, w5, w6, w7]
  ring

/-- The `i`-th word of `ofU256 r` is the pair of limbs `2i`, `2i + 1` of `r mod 2²⁵⁶`. -/
theorem ofU256_of_limbs (r : Nat) (l : Vector Nat 16) (bounded : ∀ i : Fin 16, l[i] < 65536)
    (low : value l = r % 2 ^ 256) (i : Fin 8) :
    (RV.Delegation.ofU256 r)[i] = BitVec.ofNat 32 (l[2 * i.val] + 65536 * l[2 * i.val + 1]) := by
  have b (j : Nat) (h : j < 16) : l[j] < 65536 := bounded ⟨j, h⟩
  have b0 := b 0 (by decide)
  have b1 := b 1 (by decide)
  have b2 := b 2 (by decide)
  have b3 := b 3 (by decide)
  have b4 := b 4 (by decide)
  have b5 := b 5 (by decide)
  have b6 := b 6 (by decide)
  have b7 := b 7 (by decide)
  have b8 := b 8 (by decide)
  have b9 := b 9 (by decide)
  have b10 := b 10 (by decide)
  have b11 := b 11 (by decide)
  have b12 := b 12 (by decide)
  have b13 := b 13 (by decide)
  have b14 := b 14 (by decide)
  have b15 := b 15 (by decide)
  rw [value_expand] at low
  simp only [RV.Delegation.ofU256, Vector.getElem_ofFn, Fin.getElem_fin]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  norm_num at low
  fin_cases i
  all_goals norm_num
  all_goals omega

/-- The control byte of `x12`: only the low limb's low byte counts. -/
theorem control_byte {x12 : RV.Word} {m : Nat} (low : x12.toNat % 65536 = m) (small : m < 256) :
    x12.toNat % 2 ^ 16 < 256 ∧ (x12 &&& 0xbf#32) = BitVec.ofNat 32 (m &&& 0xbf) ∧
      x12.getLsbD 6 = m.testBit 6 := by
  have byte : x12.toNat % 2 ^ 8 = m := by
    rw [← Nat.mod_mod_of_dvd x12.toNat (by decide : 2 ^ 8 ∣ 65536), low]
    exact Nat.mod_eq_of_lt small
  refine ⟨by omega, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    have bound : m &&& 0xbf < 2 ^ 32 := lt_of_le_of_lt Nat.and_le_left (by omega)
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, ← byte,
      ← Nat.and_two_pow_sub_one_eq_mod (BitVec.toNat x12) 8, Nat.and_assoc]
    rfl
  · rw [← byte, Nat.testBit_mod_two_pow]
    simp [BitVec.getLsbD]

/-- `bigintOp` on the control byte `op + 64 κ` of each operation (or none), κ the carry bit. -/
theorem bigintOp_control {c : Nat} (bit : c ≤ 1) (a b : Nat) :
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((64 * c) &&& 0xbf)) ((64 * c).testBit 6) a b = some (0, false) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((1 + 64 * c) &&& 0xbf)) ((1 + 64 * c).testBit 6) a b =
      some (a + b + c, decide (2 ^ 256 ≤ a + b + c)) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((2 + 64 * c) &&& 0xbf)) ((2 + 64 * c).testBit 6) a b =
      some (2 ^ 256 + a - (b + c), decide (a < b + c)) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((4 + 64 * c) &&& 0xbf)) ((4 + 64 * c).testBit 6) a b =
      some (2 ^ 256 + b - (a + c), decide (b < a + c)) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((8 + 64 * c) &&& 0xbf)) ((8 + 64 * c).testBit 6) a b =
      some (a * b, decide (2 ^ 256 ≤ a * b)) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((16 + 64 * c) &&& 0xbf)) ((16 + 64 * c).testBit 6) a b =
      some (a * b / 2 ^ 256, false) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((32 + 64 * c) &&& 0xbf)) ((32 + 64 * c).testBit 6) a b =
      some (a, decide (a = b)) ∧
    RV.Delegation.bigintOp (BitVec.ofNat 32 ((128 + 64 * c) &&& 0xbf)) ((128 + 64 * c).testBit 6) a b =
      some (b + c, decide (2 ^ 256 ≤ b + c)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp bit with rfl | rfl
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Airbender.Bigint.Proofs
