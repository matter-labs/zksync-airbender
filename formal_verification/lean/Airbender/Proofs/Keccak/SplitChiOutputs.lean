import Airbender.Proofs.Keccak.SplitChiEvaluation
import Airbender.Proofs.Keccak.SplitChiInputs

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

private theorem pow_two : (16 : Nat) ^ 2 = 256 := by decide
private theorem pow_three : (16 : Nat) ^ 3 = 4096 := by decide
private theorem pow_four : (16 : Nat) ^ 4 = 65536 := by decide

/-- Native retained chi output values are the exact cyclic nibble operation. -/
theorem chi5_output_value (column : Fin 5) (index : Fin 1048576) :
    ((chi5Generic.columns[5 + column.val].get? index.val).getD 0) =
      (index.val / 16 ^ column.val % 16) ^^^
        ((15 ^^^ (index.val / 16 ^ ((column.val + 1) % 5) % 16)) &&&
          (index.val / 16 ^ ((column.val + 2) % 5) % 16)) := by
  rw [chi5_output_get, Option.getD_some]
  fin_cases column
  · change (chi5GenericBlock98Pattern.toArray[digitIndex #[0, 1, 2] index.val]?).getD 0 =
        (index.val / 16 ^ 0 % 16) ^^^
          ((15 ^^^ (index.val / 16 ^ 1 % 16)) &&& (index.val / 16 ^ 2 % 16))
    rw [digitIndex_three]
    simp only [Nat.pow_zero, Nat.pow_one, pow_two, Nat.div_one]
    exact (chi5_pattern_evaluation ⟨index.val % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 16 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 256 % 16, Nat.mod_lt _ (by decide)⟩).1
  · change (chi5GenericBlock104Pattern.toArray[digitIndex #[1, 2, 3] index.val]?).getD 0 =
        (index.val / 16 ^ 1 % 16) ^^^
          ((15 ^^^ (index.val / 16 ^ 2 % 16)) &&& (index.val / 16 ^ 3 % 16))
    rw [digitIndex_three]
    simp only [Nat.pow_one, pow_two, pow_three]
    exact (chi5_pattern_evaluation ⟨index.val / 16 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 256 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 4096 % 16, Nat.mod_lt _ (by decide)⟩).2.1
  · change (chi5GenericBlock112Pattern.toArray[digitIndex #[2, 3, 4] index.val]?).getD 0 =
        (index.val / 16 ^ 2 % 16) ^^^
          ((15 ^^^ (index.val / 16 ^ 3 % 16)) &&& (index.val / 16 ^ 4 % 16))
    rw [digitIndex_three]
    simp only [pow_two, pow_three, pow_four]
    exact (chi5_pattern_evaluation ⟨index.val / 256 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 4096 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 65536 % 16, Nat.mod_lt _ (by decide)⟩).2.2.1
  · change (chi5GenericBlock120Pattern.toArray[digitIndex #[0, 3, 4] index.val]?).getD 0 =
        (index.val / 16 ^ 3 % 16) ^^^
          ((15 ^^^ (index.val / 16 ^ 4 % 16)) &&& (index.val / 16 ^ 0 % 16))
    rw [digitIndex_three]
    simp only [Nat.pow_zero, pow_three, pow_four, Nat.div_one]
    exact (chi5_pattern_evaluation ⟨index.val % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 4096 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 65536 % 16, Nat.mod_lt _ (by decide)⟩).2.2.2.1
  · change (chi5GenericBlock121Pattern.toArray[digitIndex #[0, 1, 4] index.val]?).getD 0 =
        (index.val / 16 ^ 4 % 16) ^^^
          ((15 ^^^ (index.val / 16 ^ 0 % 16)) &&& (index.val / 16 ^ 1 % 16))
    rw [digitIndex_three]
    simp only [Nat.pow_zero, Nat.pow_one, pow_four, Nat.div_one]
    exact (chi5_pattern_evaluation ⟨index.val % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 16 % 16, Nat.mod_lt _ (by decide)⟩ ⟨index.val / 65536 % 16, Nat.mod_lt _ (by decide)⟩).2.2.2.2

/-- Each output of the actual native table is chi of its actual input fields. -/
theorem chi5_native_column_operation (column : Fin 5) (index : Fin 1048576) :
    ((chi5Generic.columns[5 + column.val].get? index.val).getD 0) =
      ((chi5Generic.columns[column.val].get? index.val).getD 0) ^^^
        ((15 ^^^ ((chi5Generic.columns[(column.val + 1) % 5].get? index.val).getD 0)) &&&
          ((chi5Generic.columns[(column.val + 2) % 5].get? index.val).getD 0)) := by
  rw [chi5_input_get column index,
    chi5_input_get ⟨(column.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ index,
    chi5_input_get ⟨(column.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ index,
    Option.getD_some]
  exact chi5_output_value column index

end Airbender.Keccak.Split.Native.Fixed.Proofs
