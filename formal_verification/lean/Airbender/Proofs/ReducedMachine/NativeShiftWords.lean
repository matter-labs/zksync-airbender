import Airbender.Review.Circuits.ReducedMachine.ShiftResult
import Airbender.Proofs.ReducedMachine.NativeShiftNatural
import Airbender.Proofs.Tables.SllLowMath
import Airbender.Proofs.Tables.SllHighMath
import Airbender.Proofs.Tables.SrlHighMath
import Airbender.Proofs.ShiftBinop.SllLimbResult
import Airbender.Proofs.ShiftBinop.SrlLimbResult
import Airbender.Proofs.ShiftBinop.SraLimbResult

namespace Airbender.ReducedMachine.NativeShiftWordProofs
open Native Arithmetic Verification NativeShiftNaturalProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem packed (limb amount : Nat) (bound : limb < 65536) :
    (limb + 65536 * amount) % 65536 = limb ∧
      (limb + 65536 * amount) / 65536 = amount := by omega

/-- Reuse the checked low-limb RV32 contribution, without any table premise. -/
theorem left_low (limb amount : Nat) (bound : limb < 65536) :
    BitVec.ofNat 32 ((limb * 2 ^ amount) % 65536 +
      ((limb * 2 ^ amount / 65536) % 65536) * 65536) =
        (BitVec.ofNat 32 limb) <<< amount := by
  have key := packed limb amount bound
  simpa only [sllHighOutput,sllLowHighOutput,key.1,key.2] using
    SllLowProofs.shifted_bits (limb + 65536 * amount)

theorem left_high (limb amount : Nat) (bound : limb < 65536) :
    BitVec.ofNat 32 ((limb * 2 ^ amount) % 65536 * 65536) =
      (BitVec.ofNat 32 (limb * 65536)) <<< amount := by
  have key := packed limb amount bound
  simpa only [sllHighOutput,key.1,key.2] using
    SllHighProofs.high_bits (limb + 65536 * amount)

theorem right_low (limb amount : Nat) (bound : limb < 65536) :
    BitVec.ofNat 32 (limb / 2 ^ amount) =
      (BitVec.ofNat 32 limb) >>> amount := by
  have key := packed limb amount bound
  simpa only [srlLowOutput,key.1,key.2] using
    SrlLowProofs.low_bits (limb + 65536 * amount)

theorem right_high (limb amount : Nat) (bound : limb < 65536) :
    BitVec.ofNat 32 ((limb * 65536 / 2 ^ amount) % 65536 +
      limb / 2 ^ amount * 65536) =
        (BitVec.ofNat 32 (limb * 65536)) >>> amount := by
  have key := packed limb amount bound
  simpa only [srlHighLowOutput,srlLowOutput,key.1,key.2] using
    SrlHighProofs.shifted_bits (limb + 65536 * amount)

/-- The actual native filler includes zero shift; the original BitVec reference
    obtains zero there by shifting an all-ones word by its full width. -/
theorem filler_bits (hi : Nat) (amount : Fin 32) :
    BitVec.ofNat 32 (ShiftMode.arithmetic.filler hi amount.val) =
      if hi < 32768 then 0 else (BitVec.allOnes 32) <<< (32 - amount.val) := by
  by_cases sign : hi < 32768
  · simp [ShiftMode.filler,sign,show ¬32768 ≤ hi by omega]
  · apply BitVec.eq_of_toNat_eq
    fin_cases amount <;>
      norm_num [ShiftMode.filler,sign,show 32768 ≤ hi by omega,
        BitVec.toNat_ofNat,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]

/-- Original RV32 low-five-bit selection, independent of the unused high operand. -/
theorem word_shift_amount (word : Word) :
    (word.toBitVec.extractLsb' 0 5).toNat = word.lo % 32 := by
  norm_num [Word.toBitVec,Word.value,limbBase,BitVec.extractLsb',
    BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega

end Airbender.ReducedMachine.NativeShiftWordProofs
