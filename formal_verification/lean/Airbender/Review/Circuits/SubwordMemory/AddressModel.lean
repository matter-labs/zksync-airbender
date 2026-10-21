import Airbender.Review.Circuits.SubwordMemory.Decoder

namespace Airbender.SubwordMemory
open Arithmetic Verification
set_option autoImplicit false

/-- Actual native source, decoded immediate, byte address and containing word. -/
def sourceWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 17).val,(w 18).val⟩
def immediateWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 9).val,(w 10).val⟩
def addressWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 19).val,(w 20).val⟩
def cellWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 19 - w 22).val,(w 20).val⟩

/-- Native RV32 address addition and the actual mixed-port containing word.
    Public decoding and initialized history discharge numerical interfaces;
    original instruction execution and architectural ROM binding are separate. -/
structure NativeAddress (w : Nat → ZMod mersenne31Modulus) : Prop where
  addressBound : (addressWord w).Bounded
  cellBound : (cellWord w).Bounded
  effective : (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec
  offset : (w 22).val = (addressWord w).toBitVec.toNat % 4
  containing : (cellWord w).toBitVec.toNat = (addressWord w).toBitVec.toNat / 4 * 4
  aligned : (cellWord w).toBitVec.toNat % 4 = 0
  recombine : (cellWord w).toBitVec + BitVec.ofNat 32 (w 22).val = (addressWord w).toBitVec
  loadPort : w 12 = 0 → (⟨(w 30).val,(w 31).val⟩ : Word) = cellWord w
  storePort : w 12 = 1 → (⟨(w 35).val,(w 36).val⟩ : Word) = cellWord w

end Airbender.SubwordMemory
