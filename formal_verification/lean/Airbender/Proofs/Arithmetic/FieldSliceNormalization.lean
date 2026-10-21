import Airbender.Proofs.Arithmetic.FieldSlices

namespace Airbender.Arithmetic
set_option warningAsError true

/-- Eliminate the low digit before polynomial normalization. This shares the
    carry and packed-output recomposition across every native adapter. -/
theorem carryLow_as_value {p : Nat} [Fact p.Prime] (value : ZMod p) :
    carryLow value = value - 2 * carryHigh value := by
  linear_combination carry_recompose value

theorem combinedLow_as_value {p : Nat} [Fact p.Prime] (value : ZMod p) :
    combinedLow value = value - 16 * combinedHigh value := by
  linear_combination combined_recompose value

end Airbender.Arithmetic
