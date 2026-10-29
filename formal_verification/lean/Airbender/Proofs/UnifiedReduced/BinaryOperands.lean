import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.Binary
import Airbender.Proofs.Arithmetic.WordBytes
import Airbender.Proofs.Sail.Bytes
import Airbender.Proofs.Trace.BytePorts

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem binary_sign_byte [Fact p.Prime] (hp : FieldCapacity.NoWrap p 256)
    {initial : State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (load : w 28 = 0) :
    (w 9).val < 256 ∧ (w 57).val = if (w 9).val < 128 then 0 else 255 := by
  have gate := Verification.assertion_of_holds holds ⟨39, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, load] at gate
  have t := Verification.assertion_of_holds holds ⟨45, by rw [constraint_count]; decide⟩
  have a := Verification.assertion_of_holds holds ⟨46, by rw [constraint_count]; decide⟩
  have b := Verification.assertion_of_holds holds ⟨47, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2, other.1, other.2.1, other.2.2.1, other.2.2.2, gate] at t a b
  have tag : w 82 = 3 := by linear_combination t
  have key : w 83 = w 9 := by linear_combination a
  have value : w 84 = w 57 := by linear_combination b
  have query := Verification.lookup_of_holds holds ⟨13, by rw [lookup_count]; decide⟩
  have standard := Setup.Proofs.ordinary_lookup (by omega : 55 ≤ p) query 3 (Or.inl rfl)
    (by simpa [Expression.eval, Verification.environment] using tag)
  have sign := Verification.binary_sign_lookup hp standard
    (by simpa [Expression.eval, Verification.environment] using tag)
  simpa [Expression.eval, Verification.environment, key, value] using sign

theorem binary_left_bytes [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (inverse : SerializedInverse.Scale256 p) {initial : State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (Setup.binaryTag tag : ZMod p)) :
    ∀ i : Fin 4, leftByte w i =
      (((Word.mk (w 36).val (w 37).val).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p) := by
  have values := binary_query_values (by omega : 256 < p) holds selected other tag valid funct3
  exact Word.byte_fields hp (w 36) (w 37) (leftByte w) (fun i => (values i).1)
    (by change w 74 + 256 * (-7864320 * (w 36 - w 74)) = w 36
        linear_combination (w 36 - w 74) * inverse)
    (by change w 75 + 256 * (-7864320 * (w 37 - w 75)) = w 37
        linear_combination (w 37 - w 75) * inverse)

theorem binary_register_bytes [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (inverse : SerializedInverse.Scale256 p) {initial : State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (load : w 28 = 0) (immediate : w 8 = 0 ∧ w 9 = 0)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (Setup.binaryTag tag : ZMod p)) :
    ∀ i : Fin 4, rightByte w i + immediateByte w i =
      (((Word.mk (w 42).val (w 43).val).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p) := by
  have sign : w 57 = 0 := by
    apply ZMod.val_injective
    simpa [immediate.2] using (binary_sign_byte (by omega) holds selected other load).2
  have zero (i : Fin 4) : immediateByte w i = 0 := by
    fin_cases i <;> simp [immediateByte, immediate.1, immediate.2, sign]
  have values := binary_query_values (by omega : 256 < p) holds selected other tag valid funct3
  have rightBound (i : Fin 4) : (rightByte w i).val < 256 := by
    simpa only [zero, add_zero] using (values i).2.1
  have bytes := Word.byte_fields hp (w 42) (w 43) (rightByte w) rightBound
    (by change w 76 + 256 * (-7864320 * (w 42 - w 76)) = w 42
        linear_combination (w 42 - w 76) * inverse)
    (by change w 77 + 256 * (-7864320 * (w 43 - w 77)) = w 43
        linear_combination (w 43 - w 77) * inverse)
  simpa only [zero, add_zero] using bytes

theorem binary_immediate_bytes [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (inverse : SerializedInverse.Scale256 p) {initial : State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (load : w 28 = 0) (imm : BitVec 12)
    (immediate : w 8 = ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 0 8).toNat ∧
      w 9 = ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 8 8).toNat)
    (zeroRead : w 42 = 0 ∧ w 43 = 0)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (Setup.binaryTag tag : ZMod p)) :
    ∀ i : Fin 4, rightByte w i + immediateByte w i =
      (((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' (8 * i.val) 8).toNat : ZMod p) := by
  let x := SailRV32.Functions.sign_extend (m := 32) imm
  let byte (i : Fin 4) := rightByte w i + immediateByte w i
  let target (i : Fin 4) : ZMod p := (x.extractLsb' (8 * i.val) 8).toNat
  have small (i : Fin 4) : (byte i).val < 256 :=
    (binary_query_values (by omega) holds selected other tag valid funct3 i).2.1
  have targetSmall (i : Fin 4) : (target i).val < 256 := by
    rw [show target i = ((x.extractLsb' (8 * i.val) 8).toNat : ZMod p) from rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (x.extractLsb' (8 * i.val) 8).isLt; omega)]
    exact (x.extractLsb' (8 * i.val) 8).isLt
  have sign := (binary_sign_byte (by omega) holds selected other load).2
  have signValue : (w 57).val = if (x.extractLsb' 8 8).toNat < 128 then 0 else 255 := by
    rw [immediate.2, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (x.extractLsb' 8 8).isLt; omega)] at sign
    exact sign
  have upper (i : Fin 2) : w 57 = ((x.extractLsb' (16 + 8 * i.val) 8).toNat : ZMod p) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (x.extractLsb' (16 + 8 * i.val) 8).isLt; omega)]
    exact signValue.trans (Reference.Sail.sign_extend_high_bytes imm i).symm
  have low := Trace.Proofs.packed_bytes_unique (by omega) (small 0) (small 1) (targetSmall 0) (targetSmall 1)
    (show byte 0 + 256 * byte 1 = target 0 + 256 * target 1 by
      rw [show target 0 = w 8 from immediate.1.symm, show target 1 = w 9 from immediate.2.symm]
      change w 76 + w 8 + 256 * (-7864320 * (w 42 - w 76) + w 9) = w 8 + 256 * w 9
      rw [zeroRead.1]
      linear_combination -w 76 * inverse)
  have high := Trace.Proofs.packed_bytes_unique (by omega) (small 2) (small 3) (targetSmall 2) (targetSmall 3)
    (show byte 2 + 256 * byte 3 = target 2 + 256 * target 3 by
      rw [show target 2 = w 57 from (upper 0).symm, show target 3 = w 57 from (upper 1).symm]
      change w 77 + w 57 + 256 * (-7864320 * (w 43 - w 77) + w 57) = w 57 + 256 * w 57
      rw [zeroRead.2]
      linear_combination -w 77 * inverse)
  intro i
  fin_cases i
  all_goals first | exact low.1 | exact low.2 | exact high.1 | exact high.2

end Airbender.UnifiedReduced.Proofs
