import Airbender.Proofs.Keccak.SplitParityIotaBytes

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- All actual low bytes have the original selected-round effect, including the two unchanged bytes. -/
theorem parity_iota_low_bytes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (index : Fin 3) :
    (parityIotaInputLow w index).val < 256 ∧
      (parityIotaOutputByte cached w (parityIotaLimb index) false).val =
        (parityIotaInputLow w index).val ^^^ iotaByte (round.val + 32 * (2 * (parityIotaLimb index).val)) := by
  fin_cases index
  · exact parity_iota_low_zero cached w holds round selected
  · change (parityIotaInputLow w 1).val < 256 ∧
      (parityIotaOutputByte cached w 1 false).val = (parityIotaInputLow w 1).val ^^^ iotaByte (round.val + 64)
    have equation : parityIotaInputLow w 1 = parityIotaOutputByte cached w 1 false :=
      parity_iota_unchanged_low cached w holds 0
    rw [equation, (parity_iota_zero_parts round).1, Nat.xor_zero]
    exact ⟨parity_iota_output_byte_value cached w holds 1 false, rfl⟩
  · change (parityIotaInputLow w 2).val < 256 ∧
      (parityIotaOutputByte cached w 3 false).val = (parityIotaInputLow w 2).val ^^^ iotaByte (round.val + 192)
    have equation : parityIotaInputLow w 2 = parityIotaOutputByte cached w 3 false :=
      parity_iota_unchanged_low cached w holds 1
    rw [equation, (parity_iota_zero_parts round).2.1, Nat.xor_zero]
    exact ⟨parity_iota_output_byte_value cached w holds 3 false, rfl⟩

/-- The actual affected native read limbs have canonical bounded byte expansions. -/
theorem parity_iota_read_limb_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (index : Fin 3) :
    (parityLaneLimb cached false w 0 (parityIotaLimb index)).val < 65536 ∧
      (parityLaneLimb cached false w 0 (parityIotaLimb index)).val =
        (parityIotaInputLow w index).val + 256 * (parityIotaInputHigh cached w index).val := by
  have low := (parity_iota_low_bytes cached w holds round selected index).1
  have high := (parity_iota_high_bytes cached w holds round selected index).1
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    (parity_iota_read_packing cached w index).symm
  exact ⟨by rw [value]; omega, value⟩

/-- The three affected written limbs equal their actual reads XOR the original reference constant. -/
theorem parity_iota_affected_limb_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (index : Fin 3) :
    (parityLaneLimb cached true w 0 (parityIotaLimb index)).val =
      (parityLaneLimb cached false w 0 (parityIotaLimb index)).val ^^^
        (Call.roundConstant round.val / 65536 ^ (parityIotaLimb index).val % 65536) := by
  have low := parity_iota_low_bytes cached w holds round selected index
  have high := parity_iota_high_bytes cached w holds round selected index
  have written := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide)
    (parity_iota_output_byte_value cached w holds (parityIotaLimb index) false)
    (parity_iota_output_byte_value cached w holds (parityIotaLimb index) true)
    (parity_iota_write_packing cached w (parityIotaLimb index)).symm
  rw [written, low.2, high.2]
  have joined := xor_of_chunks (width := 8) low.1
    (show iotaByte (round.val + 32 * (2 * (parityIotaLimb index).val)) < 2 ^ 8 from Nat.mod_lt _ (by decide))
    (a₁ := (parityIotaInputHigh cached w index).val)
    (b₁ := iotaByte (round.val + 32 * (2 * (parityIotaLimb index).val + 1)))
  norm_num only [Nat.reducePow] at joined
  rw [← joined, ← (parity_iota_read_limb_value cached w holds round selected index).2,
    parity_iota_constant_limbs]

/-- Every actual first-lane read limb has a canonical sixteen-bit value. -/
theorem parity_iota_read_limb_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (limb : Fin 4) :
    (parityLaneLimb cached false w 0 limb).val < 65536 := by
  fin_cases limb
  · exact (parity_iota_read_limb_value cached w holds round selected 0).1
  · exact (parity_iota_read_limb_value cached w holds round selected 1).1
  · change (parityLaneLimb cached false w 0 (2 : Fin 4)).val < 65536
    rw [parity_iota_unchanged_limb cached w holds]
    exact (parity_write_limb_value cached w holds 0 2).1
  · exact (parity_iota_read_limb_value cached w holds round selected 2).1

/-- All four native first-lane limbs have their exact original iota effect. -/
theorem parity_iota_limb_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (limb : Fin 4) :
    (parityLaneLimb cached true w 0 limb).val = (parityLaneLimb cached false w 0 limb).val ^^^
      (Call.roundConstant round.val / 65536 ^ limb.val % 65536) := by
  fin_cases limb
  · exact parity_iota_affected_limb_operation cached w holds round selected 0
  · exact parity_iota_affected_limb_operation cached w holds round selected 1
  · change (parityLaneLimb cached true w 0 (2 : Fin 4)).val =
      (parityLaneLimb cached false w 0 (2 : Fin 4)).val ^^^ (Call.roundConstant round.val / 65536 ^ 2 % 65536)
    rw [← parity_iota_unchanged_limb cached w holds, (parity_iota_zero_parts round).2.2, Nat.xor_zero]
  · exact parity_iota_affected_limb_operation cached w holds round selected 2

/-- The complete native first-lane write equals its actual read XOR the original selected round constant. -/
theorem parity_iota_lane_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) :
    parityLaneValue cached true w 0 = parityLaneValue cached false w 0 ^^^ Call.roundConstant round.val := by
  let readValue (limb : Fin 4) := (parityLaneLimb cached false w 0 limb).val
  let constant (limb : Fin 4) := Call.roundConstant round.val / 65536 ^ limb.val % 65536
  have readBound (limb : Fin 4) : readValue limb < 2 ^ 16 :=
    parity_iota_read_limb_bound cached w holds round selected limb
  have constantBound (limb : Fin 4) : constant limb < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have outputs : (fun limb => (parityLaneLimb cached true w 0 limb).val) =
      (fun limb => readValue limb ^^^ constant limb) := by
    funext limb
    exact parity_iota_limb_operation cached w holds round selected limb
  unfold parityLaneValue
  rw [outputs, pack_four_xor _ _ readBound constantBound, parity_iota_constant_word]

end Airbender.Keccak.Split.Native.Proofs
