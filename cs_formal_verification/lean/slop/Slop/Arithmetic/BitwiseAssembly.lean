import Slop.Arithmetic.ByteAssembly

namespace Airbender.Arithmetic
set_option warningAsError true

theorem and_of_chunks {width a₀ a₁ b₀ b₁ : Nat}
    (aBound : a₀ < 2 ^ width) (bBound : b₀ < 2 ^ width) :
    (a₀ + 2 ^ width * a₁) &&& (b₀ + 2 ^ width * b₁) =
      (a₀ &&& b₀) + 2 ^ width * (a₁ &&& b₁) := by
  rw [xor_eq_add width aBound, xor_eq_add width bBound,
    xor_eq_add width (lt_of_le_of_lt Nat.and_le_left aBound)]
  rw [Nat.and_xor_distrib_left, Nat.and_xor_distrib_right,
    Nat.and_xor_distrib_right, and_mul_two_pow_lt aBound,
    Nat.and_comm (2 ^ width * a₁) b₀, and_mul_two_pow_lt bBound,
    Nat.xor_zero, Nat.zero_xor, ← and_mul_two_pow]

theorem and_of_four_chunks {width a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat}
    (a₀Bound : a₀ < 2 ^ width) (a₁Bound : a₁ < 2 ^ width) (a₂Bound : a₂ < 2 ^ width)
    (b₀Bound : b₀ < 2 ^ width) (b₁Bound : b₁ < 2 ^ width) (b₂Bound : b₂ < 2 ^ width) :
    (a₀ + 2 ^ width * (a₁ + 2 ^ width * (a₂ + 2 ^ width * a₃))) &&&
      (b₀ + 2 ^ width * (b₁ + 2 ^ width * (b₂ + 2 ^ width * b₃))) =
    (a₀ &&& b₀) + 2 ^ width * ((a₁ &&& b₁) + 2 ^ width *
      ((a₂ &&& b₂) + 2 ^ width * (a₃ &&& b₃))) := by
  rw [and_of_chunks a₀Bound b₀Bound, and_of_chunks a₁Bound b₁Bound,
    and_of_chunks a₂Bound b₂Bound]

theorem andn_of_chunks {width a₀ a₁ b₀ b₁ : Nat}
    (aBound : a₀ < 2 ^ width) (bBound : b₀ < 2 ^ width) :
    ((a₀ + 2 ^ width * a₁) ^^^ (2 ^ width - 1 + 2 ^ width * (2 ^ width - 1))) &&&
      (b₀ + 2 ^ width * b₁) =
    ((a₀ ^^^ (2 ^ width - 1)) &&& b₀) +
      2 ^ width * ((a₁ ^^^ (2 ^ width - 1)) &&& b₁) := by
  have mask : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  rw [xor_of_chunks aBound mask,
    and_of_chunks (Nat.xor_lt_two_pow aBound mask) bBound]

theorem andn_of_four_limbs {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat}
    (a₀Bound : a₀ < 65536) (a₁Bound : a₁ < 65536) (a₂Bound : a₂ < 65536)
    (b₀Bound : b₀ < 65536) (b₁Bound : b₁ < 65536) (b₂Bound : b₂ < 65536) :
    (not64 (a₀ + 65536 * (a₁ + 65536 * (a₂ + 65536 * a₃)))) &&&
      (b₀ + 65536 * (b₁ + 65536 * (b₂ + 65536 * b₃))) =
    ((a₀ ^^^ 65535) &&& b₀) + 65536 * (((a₁ ^^^ 65535) &&& b₁) + 65536 *
      (((a₂ ^^^ 65535) &&& b₂) + 65536 * ((a₃ ^^^ 65535) &&& b₃))) := by
  unfold not64
  change ((a₀ + 2 ^ 16 * (a₁ + 2 ^ 16 * (a₂ + 2 ^ 16 * a₃))) ^^^
    (65535 + 2 ^ 16 * (65535 + 2 ^ 16 * (65535 + 2 ^ 16 * 65535)))) &&& _ = _
  rw [xor_of_four_chunks a₀Bound a₁Bound a₂Bound (by decide) (by decide) (by decide)]
  have value := and_of_four_chunks (width := 16)
    (Nat.xor_lt_two_pow a₀Bound (show 65535 < 2 ^ 16 from by decide))
    (Nat.xor_lt_two_pow a₁Bound (show 65535 < 2 ^ 16 from by decide))
    (Nat.xor_lt_two_pow a₂Bound (show 65535 < 2 ^ 16 from by decide))
    b₀Bound b₁Bound b₂Bound (a₃ := a₃ ^^^ 65535) (b₃ := b₃)
  norm_num only [Nat.reducePow] at value ⊢
  exact value

end Airbender.Arithmetic
