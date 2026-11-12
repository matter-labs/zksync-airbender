module
public import Proven.Blake2Round.Mask.RVControl
public import Human.ISA.BlakeRoundMask

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The RV mask update clears the low limb, keeps the mode bits, and shifts the round bits. -/
def nextBits (control : RV.Word) : RV.Word :=
  (((control >>> 16) &&& 7#32) ||| ((((control >>> 19) <<< 1) &&& 0x3ff#32) <<< 3)) <<< 16

/-- The native arithmetic controller update equals the RV bit update for every bounded word. -/
theorem next_bits (word : Word) (bounded : word.Bounded) :
    (Control.next word).toBitVec = nextBits word.toBitVec := by
  have quotient : word.toBitVec.toNat / 65536 = word.hi := by
    rw [Word.toBitVec_toNat bounded]
    change (word.lo + 65536 * word.hi) / 65536 = word.hi
    have low := bounded.1
    change word.lo < 65536 at low
    omega
  have upper : (word.toBitVec >>> 16).toNat = word.hi := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact quotient
  have mask : (word.toBitVec >>> 19).toNat = word.hi / 8 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change word.toBitVec.toNat / (65536 * 8) = word.hi / 8
    rw [← Nat.div_div_eq_div_mul, quotient]
  have modes : ((word.toBitVec >>> 16) &&& 7#32).toNat = word.hi % 8 := by
    rw [BitVec.toNat_and, upper]
    exact Nat.and_two_pow_sub_one_eq_mod word.hi 3
  have maskShift : (((word.toBitVec >>> 19) <<< 1) &&& 0x3ff#32).toNat =
      2 * (word.hi / 8 % 512) := by
    rw [BitVec.toNat_and, BitVec.toNat_shiftLeft, mask, Nat.shiftLeft_eq]
    change ((word.hi / 8 * 2) % 2 ^ 32) &&& (2 ^ 10 - 1) = _
    have small : word.hi / 8 * 2 < 2 ^ 32 := by
      have high := bounded.2
      change word.hi < 65536 at high
      omega
    rw [Nat.mod_eq_of_lt small, Nat.and_two_pow_sub_one_eq_mod]
    norm_num only [Nat.reducePow]
    omega
  have rounds : ((((word.toBitVec >>> 19) <<< 1) &&& 0x3ff#32) <<< 3).toNat =
      16 * (word.hi / 8 % 512) := by
    rw [BitVec.toNat_shiftLeft, maskShift, Nat.shiftLeft_eq]
    norm_num only [Nat.reducePow]
    have small : 2 * (word.hi / 8 % 512) * 8 < 4294967296 := by omega
    rw [Nat.mod_eq_of_lt small]
    omega
  have packed : (((word.toBitVec >>> 16) &&& 7#32) |||
      ((((word.toBitVec >>> 19) <<< 1) &&& 0x3ff#32) <<< 3)).toNat =
      word.hi % 8 + 16 * (word.hi / 8 % 512) := by
    rw [BitVec.toNat_or, modes, rounds]
    have combine := Nat.two_pow_add_eq_or_of_lt
      (i := 3) (Nat.mod_lt word.hi (by decide : 0 < 8)) (2 * (word.hi / 8 % 512))
    norm_num only [Nat.reducePow] at combine
    rw [show 16 * (word.hi / 8 % 512) = 8 * (2 * (word.hi / 8 % 512)) by omega,
      Nat.or_comm, ← combine]
    omega
  apply BitVec.eq_of_toNat_eq
  conv_lhs => simp only [Word.toBitVec, Control.next, Word.value, limbBase, Nat.zero_add, BitVec.toNat_ofNat]
  rw [nextBits, BitVec.toNat_shiftLeft, packed, Nat.shiftLeft_eq]
  norm_num only [Nat.reducePow]
  congr 1
  omega

end Airbender.Blake2Round.Mask.Proofs
