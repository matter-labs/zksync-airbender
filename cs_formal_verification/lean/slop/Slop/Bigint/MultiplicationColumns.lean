import Slop.Bigint.MultiplicationColumns.Part0
import Slop.Bigint.MultiplicationColumns.Part1
import Slop.Bigint.MultiplicationColumns.Part2
import Slop.Bigint.MultiplicationColumns.Part3
import Slop.Bigint.MultiplicationColumns.Part4
import Slop.Bigint.MultiplicationColumns.Part5
import Slop.Bigint.MultiplicationColumns.Part6
import Slop.Bigint.MultiplicationColumns.Part7

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000

/-- Normalize each imported multiplication assertion into its byte column.
    The serialized inverse is interpreted in this artifact's BabyBear field. -/
theorem native_columns {w : Nat → ZMod babyBearModulus} {left right : Fin 16 → Nat}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (sources : ∀ i, w Variables.leftLimbs[i] = (left i : ZMod babyBearModulus) ∧
      w Variables.rightLimbs[i] = (right i : ZMod babyBearModulus))
    (bytes : ∀ i : Fin 16,
      w (99 + i.val) = ((left i % 256 : Nat) : ZMod babyBearModulus) ∧
      w (115 + i.val) = ((right i % 256 : Nat) : ZMod babyBearModulus)) :
    ∀ i : Fin 32, (multiplicationColumn left right i.val : ZMod babyBearModulus) + incoming w i =
      w (131 + i.val) + 65536 * outgoing w i := by
  intro i
  have size := i.isLt
  by_cases c0 : i.val < 4
  · exact native_columns_0 h sources bytes i (by omega) c0
  by_cases c1 : i.val < 8
  · exact native_columns_1 h sources bytes i (by omega) c1
  by_cases c2 : i.val < 12
  · exact native_columns_2 h sources bytes i (by omega) c2
  by_cases c3 : i.val < 16
  · exact native_columns_3 h sources bytes i (by omega) c3
  by_cases c4 : i.val < 20
  · exact native_columns_4 h sources bytes i (by omega) c4
  by_cases c5 : i.val < 24
  · exact native_columns_5 h sources bytes i (by omega) c5
  by_cases c6 : i.val < 28
  · exact native_columns_6 h sources bytes i (by omega) c6
  exact native_columns_7 h sources bytes i (by omega) size

end Airbender.Bigint.Multiplication.Proofs
