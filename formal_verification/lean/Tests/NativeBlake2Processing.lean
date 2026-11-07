import Airbender.Review.Circuits.Blake2Worker.ProcessingTheorems

namespace Airbender.Tests.NativeBlake2Processing
open Verification Blake2Worker Blake2Worker.Native Blake2Worker.ProcessingArtifact
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem exact_source : processingSourceBytes = constraintsSourceBytes := ProcessingProofs.same_source

theorem convention_count : (processingConstraints : List (FlatOperation (ZMod mersenne31Modulus))).length = 226 := by decide +kernel

theorem complete_memory_partition :
    (processingMultiplicity :: processingMaskedColumns.toList).Perm processingMemoryColumns.toList := ProcessingProofs.memory_partition

theorem nonboolean_rejected {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) (wrong : w 0 = 2) : False := by
  have bit : w 0 = 0 ∨ w 0 = 1 := (local_processing_effects accepted).2.multiplicityBit
  rw [wrong] at bit
  have ne0 : (2 : ZMod mersenne31Modulus) ≠ 0 := by decide +kernel
  have ne1 : (2 : ZMod mersenne31Modulus) ≠ 1 := by decide +kernel
  exact bit.elim ne0 ne1

theorem padding_clock_rejected {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) (inactive : w 0 = 0) (wrong : w 740 ≠ 0) : False := by
  exact wrong ((local_processing_effects accepted).2.paddingMemory inactive 740 (by decide +kernel))

theorem padding_read_rejected {w : Nat → ZMod mersenne31Modulus} (slot : Fin 43)
    (accepted : LocalProcessingAccepted w) (inactive : w 0 = 0)
    (wrong : w (memoryAccess slot).readValue[0] ≠ 0) : False := by
  exact wrong ((local_processing_effects accepted).2.paddingAccesses inactive slot).2.2.1

theorem padding_readtime_rejected {w : Nat → ZMod mersenne31Modulus} (slot : Fin 43)
    (accepted : LocalProcessingAccepted w) (inactive : w 0 = 0)
    (wrong : w (memoryAccess slot).readTime[1] ≠ 0) : False := by
  exact wrong ((local_processing_effects accepted).2.paddingAccesses inactive slot).2.1

theorem padding_write_rejected {w : Nat → ZMod mersenne31Modulus} (slot : Fin 43)
    (accepted : LocalProcessingAccepted w) (inactive : w 0 = 0)
    (wrong : w ((memoryAccess slot).writeValue.getD (memoryAccess slot).readValue)[1] ≠ 0) : False := by
  exact wrong ((local_processing_effects accepted).2.paddingAccesses inactive slot).2.2.2.2.2

/-- Conventions-only positive slice, not complete native worker acceptance. -/
theorem zero_conventions : FlatOperation.ConstraintsHoldFlat
    (environment (fun _ => (0 : ZMod mersenne31Modulus))) processingConstraints := by
  rw [ProcessingProofs.conventions_iff]
  simp [processingBitTerm,processingMaskTerm]

/-- Multiplicity1 leaves convention-masked values arbitrary. This does not
    supply local worker equations, memory matching, a valid clock or issuance. -/
theorem active_conventions {w : Nat → ZMod mersenne31Modulus} (active : w 0 = 1) :
    FlatOperation.ConstraintsHoldFlat (environment w) processingConstraints := by
  rw [ProcessingProofs.conventions_iff]
  change processingBitTerm 1 (w 0) = 0 ∧ ∀ column ∈ processingMaskedColumns.toList, processingMaskTerm 1 (w 0) (w column) = 0
  simp [active,processingBitTerm,processingMaskTerm]

/-- Native half-domain scaling acts on both mask factors. -/
theorem mask_scaling : processingMaskTerm (2 : ZMod mersenne31Modulus) 0 7 = -14 ∧
    processingMaskTerm (1 : ZMod mersenne31Modulus) 0 7 = -7 := by decide +kernel

/-- Non-unit normalized witness coordinates need not themselves be Boolean.
    This is source-reference algebra, not a physical verifier witness/defect. -/
theorem scaled_bit_boundary :
    processingBitTerm (2 : ZMod mersenne31Modulus) 1073741824 = 0 ∧
    (1073741824 : ZMod mersenne31Modulus) ≠ 0 ∧ (1073741824 : ZMod mersenne31Modulus) ≠ 1 := by decide +kernel

end Airbender.Tests.NativeBlake2Processing
