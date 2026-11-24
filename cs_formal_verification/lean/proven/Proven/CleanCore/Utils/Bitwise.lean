module
public import CleanCore.Utils.Bitwise

/-! # Bit lemmas the proofs cite (Clean `Clean.Utils.Bitwise`, pinned b41c196, transcribed with proofs). -/

@[expose] public section

namespace Airbender

theorem xor_eq_add {x : ℕ} (n : ℕ) (hx : x < 2^n) (y : ℕ) : x + 2^n * y = x ^^^ 2^n * y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hi : i < n
  · have : ¬(n ≤ i) := by linarith
    simp [this]
  · have : n ≤ i := by linarith
    replace hx : x < 2^i := by
      apply lt_of_lt_of_le hx
      exact Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
    rw [Nat.testBit_lt_two_pow hx]
    simp [this]

theorem and_mul_two_pow {x y n : ℕ} : 2 ^ n * (x &&& y) =  2 ^ n * x &&&  2 ^ n * y := by
  simp only [mul_comm (2 ^ n), ← Nat.shiftLeft_eq, Nat.shiftLeft_and_distrib]

theorem xor_mul_two_pow {x y n : ℕ} : 2 ^ n * (x ^^^ y) =  2 ^ n * x ^^^  2 ^ n * y := by
  simp only [mul_comm (2 ^ n), ← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]

theorem and_mul_two_pow_lt {n : ℕ} {x : ℕ} (hx : x < 2^n) (y : ℕ) : x &&& 2^n * y = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow_mul]
  by_cases h : i < n
  · simp [h]
  · have : n ≤ i := by linarith
    replace hx : x < 2^i := by
      apply lt_of_lt_of_le hx
      exact Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
    rw [Nat.testBit_lt_two_pow hx]
    simp

end Airbender
