import Airbender.Proofs.Keccak.SplitParityLimbOperation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxHeartbeats 1600000

/-- The four actual parity memory limbs form a complete lane. -/
def parityLaneValue (cached writing : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 6) : Nat :=
  packFourChunks 16 (fun limb => (parityLaneLimb cached writing w lane limb).val)

/-- The four native readonly inputs retain every actual limb. -/
theorem parity_readonly_limb (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 4) (limb : Fin 4) :
    parityLaneLimb cached true w ⟨1 + lane.val, by omega⟩ limb =
      parityLaneLimb cached false w ⟨1 + lane.val, by omega⟩ limb := by
  cases cached <;> fin_cases lane <;> fin_cases limb <;> rfl

/-- The four complete readonly lane values stay unchanged. -/
theorem parity_readonly_lane (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 4) :
    parityLaneValue cached true w ⟨1 + lane.val, by omega⟩ =
      parityLaneValue cached false w ⟨1 + lane.val, by omega⟩ := by
  unfold parityLaneValue
  congr 1
  funext limb
  rw [parity_readonly_limb]

variable [Fact babyBearModulus.Prime]

/-- Each written native parity lane has a canonical sixty-four-bit value. -/
theorem parity_write_lane_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (lane : Fin 6) :
    parityLaneValue cached true w lane < 2 ^ 64 := by
  have h0 := (parity_write_limb_value cached w holds lane 0).1
  have h1 := (parity_write_limb_value cached w holds lane 1).1
  have h2 := (parity_write_limb_value cached w holds lane 2).1
  have h3 := (parity_write_limb_value cached w holds lane 3).1
  unfold parityLaneValue packFourChunks
  norm_num only [Nat.reducePow]
  omega

/-- The actual complete parity output equals XOR of all five written operands. -/
theorem parity_native_lane_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) :
    parityLaneValue cached true w 5 = parityLaneValue cached true w 0 ^^^
      parityLaneValue cached true w 1 ^^^ parityLaneValue cached true w 2 ^^^
      parityLaneValue cached true w 3 ^^^ parityLaneValue cached true w 4 := by
  let value (lane : Fin 6) (limb : Fin 4) := (parityLaneLimb cached true w lane limb).val
  have bounds (lane : Fin 6) (limb : Fin 4) : value lane limb < 2 ^ 16 :=
    (parity_write_limb_value cached w holds lane limb).1
  have outputs : value 5 = (fun i => value 0 i ^^^ value 1 i ^^^ value 2 i ^^^ value 3 i ^^^ value 4 i) := by
    funext i
    exact parity_write_limb_operation cached w holds i
  change packFourChunks 16 (value 5) = _
  rw [outputs]
  exact pack_four_xor_five _ _ _ _ _ (bounds 0) (bounds 1) (bounds 2) (bounds 3) (bounds 4)

end Airbender.Keccak.Split.Native.Proofs
