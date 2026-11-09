module
public import CleanCore.Utils.Bitwise
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Init.Data.List.Find
public import Mathlib.Combinatorics.Enumerative.Composition

/-! # 64-bit rotation bounds (Clean `Clean.Utils.Rotation`, pinned b41c196): transcribed with proofs. -/

@[expose] public section

namespace Airbender

namespace Utils.Rotation
/--
  When shifting left by `N - o` in an N-bit context, the low `o` bits of `x`
  do not affect the result -- they get shifted past the N-bit boundary.
-/
theorem mod_shiftLeft_eq_shiftLeft_mod_pow (x o N : ℕ) (ho_lt : o < N) :
    ((x % (1 <<< o)) <<< (N - o)) % (2^N) = (x <<< (N - o)) % (2^N) := by
  simp [Nat.shiftLeft_eq]
  have h_pow : 2^o * 2^(N - o) = 2^N := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt ho_lt)]
  have h_eq : (x % 2^o * 2^(N - o)) + 2^N * (x / 2^o) = x * 2^(N - o) := by
    rw [← h_pow]
    calc
      (x % 2^o * 2^(N - o)) + (2^o * 2^(N - o)) * (x / 2^o)
          = (x % 2^o * 2^(N - o)) + 2^o * (x / 2^o) * 2^(N - o) := by ring
      _ = (x % 2^o * 2^(N - o)) + (2^o * (x / 2^o)) * 2^(N - o) := by ring
      _ = (x % 2^o + 2^o * (x / 2^o)) * 2^(N - o) := by ring
      _ = (x / 2^o * 2^o + x % 2^o) * 2^(N - o) := by
        rw [add_comm, mul_comm (2^o) (x / 2^o)]
      _ = x * 2^(N - o) := by
        rw [mul_comm (x / 2^o) (2^o), Nat.div_add_mod x (2^o)]
  apply (Nat.add_mul_mod_self_left (x % 2^o * 2^(N - o)) (2^N) (x / 2^o)).symm.trans ?_
  rw [h_eq]

/--
  Our definition of right rotation of a 64-bit integer is equal to
  the one provided by `BitVec.rotateRight`
-/
theorem rotRight64_eq_bv_rotate (x : ℕ) (h : x < 2^64) (offset : ℕ) :
    rotRight64 x offset = (x.toUInt64.toBitVec.rotateRight offset).toNat := by
  simp only [rotRight64]
  simp only [BitVec.toNat_rotateRight]
  simp only [Nat.shiftLeft_eq, Nat.mul_mod, dvd_refl, Nat.mod_mod_of_dvd]
  simp only [Nat.mod_mod, UInt64.toNat_toBitVec]

  by_cases cond : (offset % 64 = 0)
  · simp [cond, pow_zero, Nat.mod_one, tsub_zero, Nat.reducePow, zero_mul, Nat.div_one,
    zero_add, Nat.shiftRight_zero, Nat.mod_self, mul_zero, Nat.zero_mod, Nat.or_zero]
    symm
    apply Nat.mod_eq_of_lt
    linarith

  · have h1 : 2^(64-offset%64) < 2^64 := by
      apply Nat.pow_lt_pow_of_lt
      · linarith
      · simp only [tsub_lt_self_iff, Nat.ofNat_pos, true_and]
        simp [Nat.ne_zero_iff_zero_lt] at cond
        assumption
    rw [Nat.mod_eq_of_lt h1, Nat.shiftRight_eq_div_pow]
    have low_lt : x / 2 ^ (offset % 64) < 2 ^ (64 - offset % 64) := by
      rw [Nat.div_lt_iff_lt_mul (by apply Nat.two_pow_pos)]
      rw [←Nat.pow_add, Nat.sub_add_cancel (by
        have : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
        linarith)]
      linarith
    rw [mul_comm, Nat.two_pow_add_eq_or_of_lt low_lt, Nat.or_comm]
    congr
    · simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow]
      symm
      apply Nat.mod_eq_of_lt
      assumption
    rw [Nat.mul_comm]
    rw [←Nat.shiftLeft_eq, ←Nat.shiftLeft_eq, ←Nat.one_shiftLeft]

    have ho_lt : offset % 64 < 64 := Nat.mod_lt offset (by linarith)
    have h_sat : ((x % (1 <<< (offset % 64))) <<< (64 - (offset % 64))) % 2^64 =
        (x <<< (64 - (offset % 64))) % 2^64 :=
      mod_shiftLeft_eq_shiftLeft_mod_pow x (offset % 64) 64 ho_lt
    have hx_val : (x.toUInt64.toNat % 2^64) = x := by
      simp [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact h
    rw [hx_val]
    rw [←h_sat]

    have h_eq3 : (x % 1 <<< (offset % 64)) <<< (64 - offset % 64) % 2^64 =
        (x % 1 <<< (offset % 64)) <<< (64 - offset % 64) := by
      apply Nat.mod_eq_of_lt
      have eq : 64 = (offset % 64) + (64 - (offset % 64)) := by
        rw [Nat.add_sub_of_le]
        apply Nat.le_of_lt
        apply Nat.mod_lt
        linarith
      rw (occs:=.pos [4]) [eq]
      apply Nat.shiftLeft_lt
      rw [Nat.one_shiftLeft]
      apply Nat.mod_lt
      simp only [Nat.ofNat_pos, pow_pos]

    rw [h_eq3]

/--
  Alternative definition of rotRight64 using bitwise operations.
-/
theorem rotRight64_def (x : ℕ) (off : ℕ) (hx : x < 2^64) :
    rotRight64 x off = x >>> (off % 64) ||| x <<< (64 - off % 64) % 2^64 := by
  rw [rotRight64_eq_bv_rotate _ hx]
  simp only [Nat.toUInt64_eq, BitVec.toNat_rotateRight, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  rw [show x % 2^64 = x by apply Nat.mod_eq_of_lt hx]

theorem rotRight64_lt (x r : ℕ) (h : x < 2^64) :
    rotRight64 x r < 2^64 := by
  rw [rotRight64_def _ _ h]
  have := Nat.shiftRight_le x (r % 64)
  apply Nat.or_lt_two_pow <;> omega

end Utils.Rotation

end Airbender
