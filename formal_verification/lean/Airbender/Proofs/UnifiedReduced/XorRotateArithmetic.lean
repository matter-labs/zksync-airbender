import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.XorRotateQueries
import Airbender.Proofs.UnifiedReduced.BinaryOperands
import Airbender.Proofs.Arithmetic.WordRotation
import Airbender.Proofs.Arithmetic.ShiftAssembly

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem xorrot_destination [Fact p.Prime] (hp : FieldCapacity.NoWrap p 262144)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (kind : Fin 4) (funct3 : w 10 = (47 + kind.val : Nat)) (left right : BitVec 32)
    (leftBytes : ∀ i : Fin 4, leftByte w i = ((left.extractLsb' (8 * i.val) 8).toNat : ZMod p))
    (rightBytes : ∀ i : Fin 4, rightByte w i + immediateByte w i = ((right.extractLsb' (8 * i.val) 8).toNat : ZMod p)) :
    (Word.mk (w 50).val (w 51).val).toBitVec = (left ^^^ right).rotateRight #[16, 12, 8, 7][kind.val]! := by
  let parts (i j : Fin 4) := w (58 + 4 * i.val + j.val)
  let target := (left ^^^ right).rotateRight #[16, 12, 8, 7][kind.val]!
  have queries := xorrot_query_values (by omega) holds selected other kind funct3
  have values (i j : Fin 4) : (parts i j).val =
      ((rotatedByte32 (left ^^^ right) kind i).extractLsb' (8 * j.val) 8).toNat := by
    change (w (58 + 4 * i.val + j.val)).val = _
    rw [(queries i).2.2 j, ZMod.val_natCast_of_lt (by
      have := ((BitVec.ofNat 32 ((leftByte w i).val ^^^ (rightByte w i + immediateByte w i).val)).rotateRight
        #[16, 12, 8, 7][kind.val]!).extractLsb' (8 * j.val) 8 |>.isLt
      omega)]
    rw [leftBytes i, rightBytes i, ZMod.val_natCast_of_lt (by have := (left.extractLsb' (8 * i.val) 8).isLt; omega),
      ZMod.val_natCast_of_lt (by have := (right.extractLsb' (8 * i.val) 8).isLt; omega)]
    rw [← BitVec.toNat_xor, ← BitVec.extractLsb'_xor]
    have widened (byte : BitVec 8) : BitVec.ofNat 32 byte.toNat = byte.setWidth 32 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    rw [widened]
    rfl
  have small (i j : Fin 4) : (parts i j).val < 256 := by
    rw [values i j]
    exact ((rotatedByte32 (left ^^^ right) kind i).extractLsb' (8 * j.val) 8).isLt
  let pairs (limb : Fin 2) (i : Fin 4) (j : Fin 2) : ZMod p :=
    parts i ⟨(j.val + 2 * limb.val + 4 - i.val) % 4, Nat.mod_lt _ (by decide)⟩
  have low := Verification.assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2] at low high
  have lo := sum_byte_pairs hp (pairs 0) (w 50) (fun i j => small i _)
    (by dsimp [pairs, parts]; linear_combination low)
  have hi := sum_byte_pairs hp (pairs 1) (w 51) (fun i j => small i _)
    (by dsimp [pairs, parts]; linear_combination high)
  have limbValue (limb : Fin 2) :
      ∑ i : Fin 4, ((pairs limb i 0).val + 256 * (pairs limb i 1).val) =
        (target.extractLsb' (16 * limb.val) 16).toNat := by
    rw [show (target.extractLsb' (16 * limb.val) 16).toNat = _ from rotated_limb_bytes (left ^^^ right) kind limb]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [pairs]
    rw [values, values]
    simp only [Fin.val_zero, Fin.val_one, Nat.zero_add]
  have lowValue := limbValue 0
  have highValue := limbValue 1
  rw [sum_four] at lowValue highValue
  simp only [add_assoc] at lo hi lowValue highValue
  have encoding : target.toNat = (target.extractLsb' 0 16).toNat +
      65536 * (target.extractLsb' 16 16).toNat := by
    have bound := target.isLt
    simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    norm_num only [Nat.reducePow, Nat.div_one]
    omega
  apply BitVec.eq_of_toNat_eq
  change ((w 50).val + 65536 * (w 51).val) % 4294967296 = target.toNat
  rw [lo.trans lowValue, hi.trans highValue]
  norm_num only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one]
  rw [← encoding]
  exact Nat.mod_eq_of_lt target.isLt

theorem xorrot_operand_bytes [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (inverse : SerializedInverse.Scale256 p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (kind : Fin 4) (funct3 : w 10 = (47 + kind.val : Nat)) (load : w 28 = 0)
    (immediate : w 8 = 0 ∧ w 9 = 0) :
    (∀ i : Fin 4, leftByte w i =
      (((Word.mk (w 36).val (w 37).val).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p)) ∧
    (∀ i : Fin 4, rightByte w i + immediateByte w i =
      (((Word.mk (w 42).val (w 43).val).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p)) := by
  have values := xorrot_query_values (by omega) holds selected other kind funct3
  have sign : w 57 = 0 := by
    apply ZMod.val_injective
    simpa [immediate.2] using (binary_sign_byte (by omega) holds selected other load).2
  have zero (i : Fin 4) : immediateByte w i = 0 := by
    fin_cases i <;> simp [immediateByte, immediate.1, immediate.2, sign]
  constructor
  · exact Word.byte_fields hp (w 36) (w 37) (leftByte w) (fun i => (values i).1)
      (by change w 74 + 256 * (-7864320 * (w 36 - w 74)) = w 36
          linear_combination (w 36 - w 74) * inverse)
      (by change w 75 + 256 * (-7864320 * (w 37 - w 75)) = w 37
          linear_combination (w 37 - w 75) * inverse)
  · have rightBound (i : Fin 4) : (rightByte w i).val < 256 := by
      simpa only [zero, add_zero] using (values i).2.1
    have bytes := Word.byte_fields hp (w 42) (w 43) (rightByte w) rightBound
      (by change w 76 + 256 * (-7864320 * (w 42 - w 76)) = w 42
          linear_combination (w 42 - w 76) * inverse)
      (by change w 77 + 256 * (-7864320 * (w 43 - w 77)) = w 43
          linear_combination (w 43 - w 77) * inverse)
    simpa only [zero, add_zero] using bytes

end Airbender.UnifiedReduced.Proofs
