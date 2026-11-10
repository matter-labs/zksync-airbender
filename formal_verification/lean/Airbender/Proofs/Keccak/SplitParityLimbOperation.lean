import Airbender.Proofs.Keccak.SplitParityPacking
import Airbender.Proofs.Arithmetic.FiveInputXor

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Each actual queried parity nibble equals XOR of all five actual operands. -/
theorem parity_nibble_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (digit : Fin 16) :
    (parityNibble cached w 5 digit).val = (parityNibble cached w 0 digit).val ^^^
      (parityNibble cached w 1 digit).val ^^^ (parityNibble cached w 2 digit).val ^^^
      (parityNibble cached w 3 digit).val ^^^ (parityNibble cached w 4 digit).val := by
  have facts := column_parity_native_xor5_queries cached w holds digit
  simpa [parityNibble] using facts.2.2.1

/-- The actual written parity limb equals XOR of the five actual written input limbs. -/
theorem parity_write_limb_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (limb : Fin 4) :
    (parityLaneLimb cached true w 5 limb).val = (parityLaneLimb cached true w 0 limb).val ^^^
      (parityLaneLimb cached true w 1 limb).val ^^^ (parityLaneLimb cached true w 2 limb).val ^^^
      (parityLaneLimb cached true w 3 limb).val ^^^ (parityLaneLimb cached true w 4 limb).val := by
  let digit (i : Fin 4) : Fin 16 := ⟨4 * limb.val + i.val, by have := i.isLt; omega⟩
  let value (lane : Fin 6) (i : Fin 4) := (parityNibble cached w lane (digit i)).val
  have bounds (lane : Fin 6) (i : Fin 4) : value lane i < 2 ^ 4 :=
    parity_nibble_bound cached w holds lane (digit i)
  have packed (lane : Fin 6) : (parityLaneLimb cached true w lane limb).val = packFourChunks 4 (value lane) :=
    (parity_write_limb_value cached w holds lane limb).2
  rw [packed 5, packed 0, packed 1, packed 2, packed 3, packed 4]
  have outputs : value 5 = (fun i => value 0 i ^^^ value 1 i ^^^ value 2 i ^^^ value 3 i ^^^ value 4 i) := by
    funext i
    exact parity_nibble_operation cached w holds (digit i)
  rw [outputs]
  exact pack_four_xor_five _ _ _ _ _ (bounds 0) (bounds 1) (bounds 2) (bounds 3) (bounds 4)

end Airbender.Keccak.Split.Native.Proofs
