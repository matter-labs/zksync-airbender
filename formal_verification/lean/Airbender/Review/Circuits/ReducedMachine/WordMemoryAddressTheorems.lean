import Airbender.Proofs.ReducedMachine.NativeWordMemoryShape

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false

/-- Accepted actual SW constraints derive bounded, aligned RAM addresses.
    Original decoder fields, reads, values and Sail execution remain separate. -/
theorem word_store_address {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus)) :
    (wordMemoryAddressWord w).Bounded ∧ 4194304 ≤ (wordMemoryAddressWord w).value ∧
      (wordMemoryAddressWord w).value%4 = 0 := NativeWordMemoryShapeProofs.store_address holds mask

/-- Accepted actual LW constraints derive alignment and the exact native ROM
    shadow query, including RAM loads. No original public-image identity is used. -/
theorem word_load_address {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) :
    (wordMemoryAddressWord w).Bounded ∧ (wordMemoryAddressWord w).value%4 = 0 ∧
      w 64 = ((if (w 62).val < 64 then 0 else 1) : Nat) ∧
      #v[w 66,w 67] =
        (NativeFixed.wordROMValue (((w 61).val+65536*((w 62).val%64))/4)).map Nat.cast :=
  NativeWordMemoryShapeProofs.load_address holds mask

end Airbender.ReducedMachine.Native
