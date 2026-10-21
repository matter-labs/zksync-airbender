import Airbender.Proofs.SubwordMemory.AddressArithmetic
import Airbender.Proofs.SubwordMemory.OffsetValues

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Verification
set_option autoImplicit false

/-- The original raw funct3 and x0 bits make the actual offset key canonical.
    Store selection comes from its native Boolean equation. -/
theorem native_offset_key {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (functBound : (w 11).val < 8) (zeroBit : w 8 = 0 ∨ w 8 = 1) :
    (offsetKey w).val = (w 19).val + 65536 * (w 11).val +
      524288 * (1 - (w 12).val) + 1048576 * (w 8).val := by
  have low : (w 19).val < 65536 := (address_bounds native).1
  have zeroBound := boolean_val zeroBit
  have storeBound := boolean_val (store_bit native)
  have load : (1 : ZMod mersenne31Modulus) - w 12 =
      ((1 - (w 12).val : Nat) : ZMod mersenne31Modulus) := by
    rw [Nat.cast_sub storeBound,Nat.cast_one,ZMod.natCast_zmod_val]
  have field : offsetKey w = (((w 19).val + 65536 * (w 11).val +
      524288 * (1 - (w 12).val) + 1048576 * (w 8).val : Nat) : ZMod mersenne31Modulus) := by
    simp only [offsetKey,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_zmod_val,← load]
  rw [field,ZMod.val_natCast_of_lt (by change _ < 2147483647; omega)]

/-- Accepted offsets identify the exact containing aligned word, including
    addresses at the top of RV32. No cell/address/alignment premise is supplied. -/
theorem native_address {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (sourceBound : (sourceWord w).Bounded) (immediateBound : (immediateWord w).Bounded)
    (functBound : (w 11).val < 8) (zeroBit : w 8 = 0 ∨ w 8 = 1) : NativeAddress w := by
  have bounds := address_bounds native
  have key := native_offset_key native functBound zeroBit
  have offset := (accepted_offset_values native).offset
  rw [key] at offset
  have lowOffset : (w 22).val = (w 19).val % 4 := by omega
  have offsetLe : (w 22).val ≤ (w 19).val := by omega
  have cell : (w 19 - w 22).val = (w 19).val - (w 22).val := by
    have field : w 19 - w 22 = (((w 19).val - (w 22).val : Nat) : ZMod mersenne31Modulus) := by
      rw [Nat.cast_sub offsetLe,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
    rw [field,ZMod.val_natCast_of_lt (by have := bounds.1; change _ < 2147483647; change (w 19).val < 65536 at this; omega)]
  have cellBound : (cellWord w).Bounded := by
    change (w 19 - w 22).val < 65536 ∧ (w 20).val < 65536
    rw [cell]
    exact ⟨by have := bounds.1; change (w 19).val < 65536 at this; omega,bounds.2⟩
  have addressNat := Word.toBitVec_toNat bounds
  have cellNat := Word.toBitVec_toNat cellBound
  have containing : (cellWord w).toBitVec.toNat = (addressWord w).toBitVec.toNat / 4 * 4 := by
    rw [addressNat,cellNat]
    dsimp [cellWord,addressWord,Word.value,limbBase]
    rw [cell]
    omega
  have actualOffset : (w 22).val = (addressWord w).toBitVec.toNat % 4 := by
    rw [addressNat]
    dsimp [addressWord,Word.value,limbBase]
    omega
  have recombine : (cellWord w).toBitVec + BitVec.ofNat 32 (w 22).val = (addressWord w).toBitVec := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,cellNat,BitVec.toNat_ofNat,addressNat]
    dsimp [cellWord,addressWord,Word.value,limbBase]
    rw [cell]
    have wordBound := Word.value_lt bounds
    dsimp [addressWord,Word.value,limbBase,wordModulus] at wordBound
    have small : (w 22).val < 4294967296 := by omega
    rw [Nat.mod_eq_of_lt small]
    have sum : (w 19).val - (w 22).val + 65536 * (w 20).val + (w 22).val =
        (w 19).val + 65536 * (w 20).val := by omega
    rw [sum,Nat.mod_eq_of_lt wordBound]
  have ports := port_addresses native
  refine ⟨bounds,cellBound,effective_address native sourceBound immediateBound,
    actualOffset,containing,?_,recombine,?_,?_⟩
  · rw [containing]; omega
  · intro load
    have low : w 30 = w 19 - w 22 := by simpa only [load,sub_zero,mul_one,mul_zero,add_zero] using ports.1
    have high : w 31 = w 20 := by simpa only [load,sub_zero,mul_one] using ports.2.1
    simp only [cellWord,low,high]
  · intro store
    have low : w 35 = w 19 - w 22 := by simpa only [store,sub_self,mul_one,mul_zero,add_zero] using ports.2.2.1
    have high : w 36 = w 20 := by simpa only [store,mul_one] using ports.2.2.2.1
    simp only [cellWord,low,high]

end Airbender.SubwordMemory.Proofs
