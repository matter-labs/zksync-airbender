import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Arithmetic.Chunks

namespace Airbender.Arithmetic
set_option warningAsError true

/-- A bounded two-chunk field equation fixes the canonical integer value. -/
theorem value_of_bounded_pair {p radix capacity : Nat} [Fact p.Prime]
    (hp : FieldCapacity.AtLeast p (radix * capacity)) {x low high : ZMod p}
    (lowBound : low.val < radix) (highBound : high.val < capacity)
    (equation : low + (radix : ZMod p) * high = x) :
    x.val = low.val + radix * high.val := by
  have small : low.val + radix * high.val < p := by
    have upper := Nat.mul_le_mul_left radix (by omega : high.val + 1 ≤ capacity)
    calc
      _ < radix + radix * high.val := Nat.add_lt_add_right lowBound _
      _ = radix * (high.val + 1) := by ring
      _ ≤ radix * capacity := upper
      _ ≤ p := hp
  have field : ((low.val + radix * high.val : Nat) : ZMod p) = x := by
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] using equation
  exact (congrArg ZMod.val field).symm.trans (ZMod.val_natCast_of_lt small)

/-- Reuse Clean's XOR chunk decomposition for a four-limb word. -/
theorem xor_of_four_chunks {width a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat}
    (a₀Bound : a₀ < 2 ^ width) (a₁Bound : a₁ < 2 ^ width) (a₂Bound : a₂ < 2 ^ width)
    (b₀Bound : b₀ < 2 ^ width) (b₁Bound : b₁ < 2 ^ width) (b₂Bound : b₂ < 2 ^ width) :
    (a₀ + 2 ^ width * (a₁ + 2 ^ width * (a₂ + 2 ^ width * a₃))) ^^^
      (b₀ + 2 ^ width * (b₁ + 2 ^ width * (b₂ + 2 ^ width * b₃))) =
    (a₀ ^^^ b₀) + 2 ^ width * ((a₁ ^^^ b₁) + 2 ^ width *
      ((a₂ ^^^ b₂) + 2 ^ width * (a₃ ^^^ b₃))) := by
  rw [xor_of_chunks a₀Bound b₀Bound, xor_of_chunks a₁Bound b₁Bound,
    xor_of_chunks a₂Bound b₂Bound]

end Airbender.Arithmetic
