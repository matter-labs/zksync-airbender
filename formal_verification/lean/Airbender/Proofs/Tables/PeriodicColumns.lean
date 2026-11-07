import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

/-- A nonnegative native periodic block is read at its stored template and cycle. -/
theorem periodic_get (values : Array Nat) (count stride n : Nat)
    (positive : 0 < values.size) (bound : n < count * values.size) :
    Block.get? (.periodic count (stride : Int) values) n =
      some (values[n % values.size]'(Nat.mod_lt _ positive) + stride * (n / values.size)) := by
  have inside : n % values.size < values.size := Nat.mod_lt _ positive
  simp only [Block.get?, Block.length, if_pos bound, Array.getElem?_eq_getElem inside,
    Option.getD_some]
  have casts : (values[n % values.size] : Int) + (stride : Int) * (n / values.size : Nat) =
      ((values[n % values.size] + stride * (n / values.size) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
  rw [← Int.natCast_ediv, casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

end Airbender.Setup.Proofs
