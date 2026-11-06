module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Linarith

/-! # 64- and 32-bit word operations on naturals (Clean `Clean.Utils.Bitwise`, pinned 93c9d1e): the operations the
Keccak-f[1600] and BLAKE3/Blake2s specs use, and the lemmas our proofs cite; transcribed with proofs. -/

@[expose] public section

namespace Airbender

def not64 (a : ℕ) : ℕ := a ^^^ 0xffffffffffffffff

def add32 (a b : ℕ) : ℕ := (a + b) % 2^32

def rotRight64 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 64
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(64-offset)) + high

def rotRight32 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 32
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(32-offset)) + high

def rotLeft64 (value : ℕ) (left : Fin 64) : ℕ:=
  let right := (64 - left) % 64
  rotRight64 value right

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
