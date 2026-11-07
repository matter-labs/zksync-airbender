import Airbender.Proofs.ReducedMachine.NativeWordMemoryNumerics
import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryPlatform

namespace Airbender.ReducedMachine.NativeWordMemoryPlatformProofs
open Native Arithmetic Verification Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Fresh actual native address bounds put ROM below BOTH pinned MMIO windows. -/
theorem rom_ordinary {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (inside : (wordMemoryAddressWord w).hi < 64) : OrdinaryWordAddress (wordMemoryAddressWord w).toBitVec := by
  have bounds := NativeWordMemoryNumericalProofs.address_bounds holds
  rw [OrdinaryWordAddress,Word.toBitVec_toNat bounds]
  change ((wordMemoryAddressWord w).value < 33554432 ∨ 33603584 ≤ (wordMemoryAddressWord w).value) ∧
    ((wordMemoryAddressWord w).value < 201326592 ∨ 201326624 ≤ (wordMemoryAddressWord w).value)
  have low := bounds.1
  dsimp [Word.value,limbBase] at *
  constructor <;> left <;> omega

end Airbender.ReducedMachine.NativeWordMemoryPlatformProofs
