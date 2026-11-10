import Airbender.Proofs.Arithmetic.FieldChunks

namespace Airbender.Arithmetic
set_option warningAsError true

/-- A bounded four-nibble field equation fixes the canonical sixteen-bit value. -/
theorem value_of_four_nibbles {p : Nat} [Fact p.Prime] (capacity : 65536 ≤ p)
    {x a b c d : ZMod p} (ha : a.val < 16) (hb : b.val < 16) (hc : c.val < 16) (hd : d.val < 16)
    (equation : x = a + 16 * b + 256 * c + 4096 * d) :
    x.val = a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) := by
  have small : a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) < p :=
    lt_of_lt_of_le (by omega : _ < 65536) capacity
  have cast : ((a.val + 16 * (b.val + 16 * (c.val + 16 * d.val)) : Nat) : ZMod p) = x := by
    rw [equation]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [← cast]
  exact ZMod.val_natCast_of_lt small

end Airbender.Arithmetic
