import Airbender.Proofs.Keccak.SplitParityIotaConstraints

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The unchanged native bytes and limb contain no round-constant bits. -/
theorem parity_iota_zero_parts : ∀ round : Fin 32,
    iotaByte (round.val + 64) = 0 ∧ iotaByte (round.val + 192) = 0 ∧
      Call.roundConstant round.val / 65536 ^ 2 % 65536 = 0 := by
  decide +kernel

/-- The actual affected byte constants assemble to the original reference limbs. -/
theorem parity_iota_constant_limbs : ∀ (round : Fin 32) (index : Fin 3),
    iotaByte (round.val + 32 * (2 * (parityIotaLimb index).val)) +
      256 * iotaByte (round.val + 32 * (2 * (parityIotaLimb index).val + 1)) =
        Call.roundConstant round.val / 65536 ^ (parityIotaLimb index).val % 65536 := by
  decide +kernel

/-- All four reference limbs assemble to the original complete round constant. -/
theorem parity_iota_constant_word : ∀ round : Fin 32,
    packFourChunks 16 (fun limb => Call.roundConstant round.val / 65536 ^ limb.val % 65536) =
      Call.roundConstant round.val := by
  decide +kernel

variable [Fact babyBearModulus.Prime]

/-- The actual byte query has its canonical controller-selected control value. -/
theorem parity_iota_control_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (round : Fin 32) (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus))
    (index : Fin 4) :
    (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[1].val =
      round.val + 32 * parityIotaPosition index := by
  have field : (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[1] =
      ((round.val + 32 * parityIotaPosition index : Nat) : ZMod babyBearModulus) := by
    rw [parity_iota_query_control, selected, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have small : round.val + 32 * parityIotaPosition index < babyBearModulus := by
    have bound := round.isLt
    fin_cases index <;> dsimp [parityIotaPosition] <;> unfold babyBearModulus <;> omega
  rw [field, ZMod.val_natCast_of_lt small]

/-- Native query membership fixes each actual bounded input and output byte. -/
theorem parity_iota_byte_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (index : Fin 4) :
    let row := parityQueryRow cached w ⟨2 + index.val, by omega⟩
    row[0].val < 256 ∧ row[2].val < 256 ∧
      row[2].val = row[0].val ^^^ iotaByte (round.val + 32 * parityIotaPosition index) := by
  have facts := column_parity_native_iota_queries cached w holds index
  change (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[0].val < 256 ∧
    (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[1].val < 256 ∧
    (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[2].val < 256 ∧
    (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[2].val =
      (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[0].val ^^^
        iotaByte (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[1].val at facts
  rw [parity_iota_control_value cached w round selected index] at facts
  exact ⟨facts.1, facts.2.2.1, facts.2.2.2⟩

/-- The first native low-byte query has its exact original round-constant effect. -/
theorem parity_iota_low_zero (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) :
    (parityIotaInputLow w 0).val < 256 ∧
      (parityIotaOutputByte cached w 0 false).val = (parityIotaInputLow w 0).val ^^^ iotaByte round.val := by
  have facts := parity_iota_byte_operation cached w holds round selected 0
  change (parityQueryRow cached w 2)[0].val < 256 ∧ (parityQueryRow cached w 2)[2].val < 256 ∧
    (parityQueryRow cached w 2)[2].val = (parityQueryRow cached w 2)[0].val ^^^ iotaByte (round.val + 32 * 0) at facts
  rw [(parity_iota_low_query cached w).1, (parity_iota_low_query cached w).2] at facts
  simpa only [Nat.mul_zero, Nat.add_zero] using And.intro facts.1 facts.2.2

/-- Each actual high-byte query has its exact original selected-round effect. -/
theorem parity_iota_high_bytes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (round : Fin 32)
    (selected : (parityQueryRow cached w 1)[3] = (round.val : ZMod babyBearModulus)) (index : Fin 3) :
    (parityIotaInputHigh cached w index).val < 256 ∧
      (parityIotaOutputByte cached w (parityIotaLimb index) true).val =
        (parityIotaInputHigh cached w index).val ^^^
          iotaByte (round.val + 32 * (2 * (parityIotaLimb index).val + 1)) := by
  have facts := parity_iota_byte_operation cached w holds round selected ⟨index.val + 1, by omega⟩
  have same : (⟨2 + (index.val + 1), by omega⟩ : Fin 22) = ⟨3 + index.val, by omega⟩ := by
    apply Fin.ext; dsimp; omega
  have position : parityIotaPosition ⟨index.val + 1, by omega⟩ = 2 * (parityIotaLimb index).val + 1 := by
    fin_cases index <;> rfl
  dsimp only at facts
  rw [same, parity_iota_high_query, position] at facts
  exact ⟨facts.1, facts.2.2⟩

end Airbender.Keccak.Split.Native.Proofs
