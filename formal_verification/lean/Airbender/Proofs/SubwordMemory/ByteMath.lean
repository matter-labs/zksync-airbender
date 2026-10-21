import Airbender.Proofs.Sail.Memory
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Verification
open Airbender.Arithmetic
set_option autoImplicit false

-- Both statements and proof bodies below are unchanged from the pinned v3
-- mathematical layer. No native v3 key, field, table or circuit is imported.
theorem extend_subword_limbs (byte signed : Bool) (value : Nat)
    (bound : value < (if byte then 256 else 65536)) :
    let negative := signed = true ∧ (if byte then 128 else 32768) ≤ value
    let result := Word.mk (value + if byte && negative then 65280 else 0)
      (if negative then 65535 else 0)
    result.Bounded ∧ result.toBitVec =
      if byte then SailRV32.Functions.extend_value (!signed) (BitVec.ofNat 8 value)
      else SailRV32.Functions.extend_value (!signed) (BitVec.ofNat 16 value) := by
  dsimp only
  cases byte <;> cases signed
  all_goals
    simp at bound ⊢
    constructor
    · simp [Word.Bounded, limbBase]
      first | omega | (split_ifs <;> omega)
    · apply BitVec.eq_of_toNat_eq
      simp only [Word.toBitVec, Word.value, limbBase, SailRV32.Functions.extend_value,
        SailRV32.Functions.zero_extend, SailRV32.Functions.sign_extend, Sail.BitVec.zeroExtend,
        Sail.BitVec.signExtend, Bool.false_eq_true, if_false, if_true,
        BitVec.zeroExtend, BitVec.toNat_signExtend, BitVec.msb_eq_decide,
        BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Bool.false_and,
        Bool.true_and, Bool.and_true, Bool.and_false, Bool.decide_coe]
      have canonical : value % 65536 = value := Nat.mod_eq_of_lt (by omega)
      try rw [canonical]
      first | omega | (split_ifs <;> norm_num at * <;> omega)

theorem subword_extract (byte highHalf highByte : Bool) (word : Word) (bound : word.Bounded)
    (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let half := if highHalf then word.hi else word.lo
    if byte then
      (word.toBitVec >>> (8 * offset)).setWidth 8 = BitVec.ofNat 8 (half / (if highByte then 256 else 1))
    else (word.toBitVec >>> (8 * offset)).setWidth 16 = BitVec.ofNat 16 half := by
  have canonical := Word.toBitVec_toNat bound
  have lo := bound.1
  have hi := bound.2
  unfold limbBase at lo hi
  cases byte <;> cases highHalf <;> cases highByte
  all_goals first
    | (have := aligned rfl; contradiction)
    | (simp only [Bool.false_eq_true, if_false, if_true]
       apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, canonical]
       norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.div_one, Nat.shiftRight_eq_div_pow]
       unfold Word.value limbBase
       omega)

end Airbender.Verification
