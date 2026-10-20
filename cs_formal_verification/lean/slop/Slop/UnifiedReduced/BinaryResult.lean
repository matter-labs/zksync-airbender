import Slop.UnifiedReduced.Binary

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

theorem binary_destination [Fact p.Prime] (hp : 65536 < p)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p} {left right : BitVec 32}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (Setup.binaryTag tag : ZMod p))
    (leftBytes : ∀ i : Fin 4, leftByte w i = ((left.extractLsb' (8 * i.val) 8).toNat : ZMod p))
    (rightBytes : ∀ i : Fin 4, rightByte w i + immediateByte w i =
      ((right.extractLsb' (8 * i.val) 8).toNat : ZMod p)) :
    (Word.mk (w 50).val (w 51).val).toBitVec = byteOperation tag left right := by
  let result := byteOperation tag left right
  have values := binary_query_values (by omega : 256 < p) holds selected other tag valid funct3
  have bytes (i : Fin 4) : (w (58 + 4 * i.val)).val = (result.extractLsb' (8 * i.val) 8).toNat := by
    have value := values i
    rw [leftBytes i, rightBytes i] at value
    have lb := (left.extractLsb' (8 * i.val) 8).isLt
    have rb := (right.extractLsb' (8 * i.val) 8).isLt
    have lc : (((left.extractLsb' (8 * i.val) 8).toNat : ZMod p)).val =
        (left.extractLsb' (8 * i.val) 8).toNat := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have rc : (((right.extractLsb' (8 * i.val) 8).toNat : ZMod p)).val =
        (right.extractLsb' (8 * i.val) 8).toNat := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [lc, rc] at value
    have equal := congrArg BitVec.toNat value.2.2.2.1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.2.2.1, BitVec.ofNat_toNat,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.setWidth_eq] at equal
    rw [equal]
    rcases valid with rfl | rfl | rfl
    all_goals simp [result, byteOperation, BitVec.extractLsb'_xor, BitVec.extractLsb'_or, BitVec.extractLsb'_and]
  have zero (i : Fin 4) (j : Fin 3) := (values i).2.2.2.2 j
  have z59 := zero ⟨0, by decide⟩ ⟨0, by decide⟩; have z60 := zero ⟨0, by decide⟩ ⟨1, by decide⟩; have z61 := zero ⟨0, by decide⟩ ⟨2, by decide⟩
  have z63 := zero ⟨1, by decide⟩ ⟨0, by decide⟩; have z64 := zero ⟨1, by decide⟩ ⟨1, by decide⟩; have z65 := zero ⟨1, by decide⟩ ⟨2, by decide⟩
  have z67 := zero ⟨2, by decide⟩ ⟨0, by decide⟩; have z68 := zero ⟨2, by decide⟩ ⟨1, by decide⟩; have z69 := zero ⟨2, by decide⟩ ⟨2, by decide⟩
  have z71 := zero ⟨3, by decide⟩ ⟨0, by decide⟩; have z72 := zero ⟨3, by decide⟩ ⟨1, by decide⟩; have z73 := zero ⟨3, by decide⟩ ⟨2, by decide⟩
  norm_num only at z59 z60 z61 z63 z64 z65 z67 z68 z69 z71 z72 z73
  have low := Verification.assertion_of_holds holds ⟨27, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨28, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2, z59, z65, z68, z69, z71, z72] at low
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2, z60, z61, z63, z64, z67, z73] at high
  have lo := byte_pair_value hp (w 58) (w 62) (w 50) (values 0).2.2.1 (values 1).2.2.1
    (by linear_combination low)
  have hi := byte_pair_value hp (w 66) (w 70) (w 51) (values 2).2.2.1 (values 3).2.2.1
    (by linear_combination high)
  apply BitVec.eq_of_toNat_eq
  change ((w 50).val + limbBase * (w 51).val) % 4294967296 = result.toNat
  have b0 : (w 58).val = (result.extractLsb' 0 8).toNat := bytes 0
  have b1 : (w 62).val = (result.extractLsb' 8 8).toNat := bytes 1
  have b2 : (w 66).val = (result.extractLsb' 16 8).toNat := bytes 2
  have b3 : (w 70).val = (result.extractLsb' 24 8).toNat := bytes 3
  have packed : (w 50).val + limbBase * (w 51).val = result.toNat := by
    rw [lo, hi, b0, b1, b2, b3, bytes_value result]
    simp only [limbBase]
    ring
  rw [packed, Nat.mod_eq_of_lt result.isLt]

end Airbender.UnifiedReduced.Proofs
