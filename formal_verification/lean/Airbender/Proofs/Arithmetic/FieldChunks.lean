import Airbender.Proofs.Arithmetic.Chunks

set_option warningAsError true

namespace Airbender.Arithmetic

/-- Bounded chunks recover the canonical value from a field equation. This
    also handles rechunking when no inverse occurs in the imported equation. -/
theorem value_of_chunks {p radix capacity : Nat} [Fact p.Prime]
    (hp : radix * capacity ≤ p) {x low high : ZMod p}
    (lowBound : low.val < radix) (highBound : high.val < capacity)
    (equation : x = low + radix * high) :
    x.val = low.val + radix * high.val := by
  have small : low.val + radix * high.val < p := by
    calc
      _ < radix + radix * high.val := Nat.add_lt_add_right lowBound _
      _ = radix * (high.val + 1) := by ring
      _ ≤ radix * capacity := Nat.mul_le_mul_left _ (by omega)
      _ ≤ p := hp
  have cast : ((low.val + radix * high.val : Nat) : ZMod p) = x := by
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] using equation.symm
  rw [← cast]
  exact ZMod.val_natCast_of_lt small

end Airbender.Arithmetic
