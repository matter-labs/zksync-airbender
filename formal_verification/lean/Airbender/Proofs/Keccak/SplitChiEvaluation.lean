import Airbender.Proofs.Keccak.SplitChiRows

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536

private theorem array_value {size : Nat} (values : Vector Nat size) (index : Fin size)
    (result : Nat) (equal : values[index] = result) :
    (values.toArray[index.val]?).getD 0 = result := by
  rw [Array.getElem?_eq_getElem (by simpa only [Vector.size_toArray] using index.isLt),
    Option.getD_some]
  exact equal

/-- The native indexed patterns evaluate the exact three-input nibble operation. -/
theorem chi5_pattern_evaluation (a b c : Fin 16) :
    let index := a.val + 16 * b.val + 256 * c.val
    (chi5GenericBlock98Pattern.toArray[index]?).getD 0 = a.val ^^^ ((15 ^^^ b.val) &&& c.val) ∧
    (chi5GenericBlock104Pattern.toArray[index]?).getD 0 = a.val ^^^ ((15 ^^^ b.val) &&& c.val) ∧
    (chi5GenericBlock112Pattern.toArray[index]?).getD 0 = a.val ^^^ ((15 ^^^ b.val) &&& c.val) ∧
    (chi5GenericBlock120Pattern.toArray[index]?).getD 0 = b.val ^^^ ((15 ^^^ c.val) &&& a.val) ∧
    (chi5GenericBlock121Pattern.toArray[index]?).getD 0 = c.val ^^^ ((15 ^^^ a.val) &&& b.val) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  let index : Fin 4096 := ⟨a.val + 16 * b.val + 256 * c.val, by omega⟩
  have first : index.val % 16 = a.val := by dsimp only [index]; omega
  have second : index.val / 16 % 16 = b.val := by dsimp only [index]; omega
  have third : index.val / 256 % 16 = c.val := by dsimp only [index]; omega
  have found := chi5_output_patterns index
  dsimp only at found
  rw [first, second, third] at found
  exact ⟨array_value _ index _ found.1,
    array_value _ index _ found.2.1,
    array_value _ index _ found.2.2.1,
    array_value _ index _ found.2.2.2.1,
    array_value _ index _ found.2.2.2.2⟩

end Airbender.Keccak.Split.Native.Fixed.Proofs
