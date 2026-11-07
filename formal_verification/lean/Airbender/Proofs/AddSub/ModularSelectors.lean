import Airbender.Review.Circuits.AddSub.Modular.Decoder
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

namespace Airbender.AddSub.Modular.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxHeartbeats 2000000

/-- Native custom-operation masks contain exactly the selected bit. -/
theorem native_mask_bit (opcode : Opcode) (rs1 rs2 rd : BitVec 5)
    (k : Nat) (lower : 10 ≤ k) :
    (nativeData opcode rs1 rs2 rd).mask.testBit (k - 10) =
      decide (k = if rd = 0 then 10 else opcode.selector) := by
  by_cases zero : rd = 0
  · simp only [nativeData, arithmeticFields, zero, if_true]
    rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    have same : (0 = k - 10) ↔ k = 10 := by omega
    simp only [same]
  · simp only [nativeData, arithmeticFields, zero, if_false]
    rw [Nat.testBit_two_pow]
    have bound : 10 ≤ opcode.selector := by cases opcode <;> decide
    have same : (opcode.selector - 10 = k - 10) ↔ k = opcode.selector := by omega
    simp only [same]

/-- The standalone selector array is the contiguous interval 10 through 18. -/
theorem native_selector_index (k : Nat) (lower : 10 ≤ k) (upper : k ≤ 18) :
    (#[10, 11, 12, 13, 14, 15, 16, 17, 18] : Array Nat)[k - 10]'(by change k - 10 < 9; omega) = k := by
  interval_cases k <;> rfl

end Airbender.AddSub.Modular.Proofs
