import Clean.Specs.BLAKE3

namespace Airbender.Arithmetic

/-- Assemble XOR chunks without duplicating the bitwise semantics used by Clean. -/
theorem xor_of_chunks {width a₀ a₁ b₀ b₁ : Nat}
    (aBound : a₀ < 2 ^ width) (bBound : b₀ < 2 ^ width) :
    (a₀ + 2 ^ width * a₁) ^^^ (b₀ + 2 ^ width * b₁) =
      (a₀ ^^^ b₀) + 2 ^ width * (a₁ ^^^ b₁) := by
  rw [xor_eq_add width aBound, xor_eq_add width bBound,
    xor_eq_add width (Nat.xor_lt_two_pow aBound bBound), xor_mul_two_pow]
  ac_rfl

/-- Clean's rotation moves the low chunk to the top and the high chunk to the bottom. -/
theorem rotate_right_of_chunks {width low high : Nat} (widthBound : width < 32)
    (lowBound : low < 2 ^ width) :
    rotRight32 (low + 2 ^ width * high) width = low * 2 ^ (32 - width) + high := by
  simp [rotRight32, Nat.mod_eq_of_lt widthBound, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left, Nat.mod_eq_of_lt lowBound, Nat.div_eq_of_lt lowBound]

end Airbender.Arithmetic
