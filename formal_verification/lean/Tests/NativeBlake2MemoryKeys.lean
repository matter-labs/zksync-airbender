import Airbender.Review.Circuits.Blake2Worker.MemoryKeysTheorems

namespace Airbender.Tests.NativeBlake2MemoryKeys
open Verification Blake2Worker Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem complete_descriptor_order : keyDescriptors.size = 43 ∧
    (keyDescriptor ⟨0,by decide⟩).location = .register 10 ∧
    (keyDescriptor ⟨25,by decide⟩).location = .register 11 ∧
    (keyDescriptor ⟨42,by decide⟩).location = .register 12 := by decide +kernel

theorem state_and_message_bases :
    (keyDescriptor ⟨1,by decide⟩).location = .indirect #v[2,3] 0 ∧
    (keyDescriptor ⟨24,by decide⟩).location = .indirect #v[2,3] 92 ∧
    (keyDescriptor ⟨41,by decide⟩).location = .indirect #v[100,101] 60 := by decide +kernel

theorem every_access_is_original (slot : Fin 43) :
    (keyDescriptor slot).access = memoryAccess slot := (MemoryKeyProofs.descriptors slot).2

theorem readonly_register_refresh (w : Nat → ZMod mersenne31Modulus) :
    (quotientMemoryKey w ⟨0,by decide⟩ false).value = #v[w 2,w 3] ∧
    (quotientMemoryKey w ⟨0,by decide⟩ true).value = #v[w 2,w 3] ∧
    (quotientMemoryKey w ⟨0,by decide⟩ false).time = #v[w 743,w 744] ∧
    (quotientMemoryKey w ⟨0,by decide⟩ true).time = #v[w 740,w 741] := by
  simp [quotientMemoryKey,keyValue,keyTime,memoryAccess,memoryAccesses,constraintsABI]

theorem control_oldread_write (w : Nat → ZMod mersenne31Modulus) :
    (quotientMemoryKey w ⟨42,by decide⟩ false).value = #v[w 134,w 135] ∧
    (quotientMemoryKey w ⟨42,by decide⟩ true).value = #v[w 136,w 137] ∧
    (quotientMemoryKey w ⟨42,by decide⟩ false).time = #v[w 869,w 870] := by
  simp [quotientMemoryKey,keyValue,keyTime,memoryAccess,memoryAccesses,constraintsABI]

private def widePointer (column : Nat) : ZMod mersenne31Modulus := if column = 2 then 65536 else 0

/-- Reference key boundary only: active correspondence needs initialized reads.
    This is not a complete accepted worker row or native defect. -/
theorem uninitialized_wide_pointer_boundary :
    stageTwoKeyAddress widePointer (.indirect #v[2,3] 4) = some ⟨0,4,0⟩ ∧
    quotientKeyAddress widePointer (.indirect #v[2,3] 4) = ⟨0,65540,0⟩ := by decide +kernel

/-- Selected offset4 with a deliberately unaligned reference base. No native
    worker acceptance is asserted by this arithmetic conversion test. -/
theorem stage_two_carry_boundary : stageTwoIndirectAddress 65535 0 4 = some ⟨0,3,1⟩ := by decide +kernel

theorem stage_two_high_overflow : stageTwoIndirectAddress 65535 65535 4 = none := by decide +kernel

theorem unused_keys_agree {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) (zero : w 0 = 0) (slot : Fin 43) :
    stageTwoMemoryKey w slot false = stageTwoMemoryKey w slot true := by
  have law := padding_memory_keys accepted
  rw [law.readKeys zero slot,law.writeKeys zero slot,law.equalKeys zero slot]

theorem wrong_unused_key_rejected {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) (zero : w 0 = 0) (slot : Fin 43)
    (wrong : quotientMemoryKey w slot false ≠ quotientMemoryKey w slot true) : False :=
  wrong ((padding_memory_keys accepted).equalKeys zero slot)

private def zeroChallenges : MemoryKeyChallenges (ZMod mersenne31Modulus) := ⟨0,0,0,0,0,0,0⟩

/-- Equality of products does not grant nonzero factors or a defined ratio. -/
theorem zero_factor_boundary : memoryKeyArgument (RingHom.id _) zeroChallenges
    ⟨⟨0,4,0⟩,#v[0,0],#v[0,0]⟩ = 0 := by decide +kernel

theorem all_factors_retained {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) (zero : w 0 = 0) :
    memoryKeyProduct embed ch w true = memoryKeyProduct embed ch w false :=
  padding_memory_products embed ch accepted zero

end Airbender.Tests.NativeBlake2MemoryKeys
