import Airbender.Proofs.Blake2Worker.NativeMemoryKeys

namespace Airbender.Blake2Worker.Native
open Verification

/-- The stronger ordinary-row normalized processing contract derives agreement
    and cancellation of every unused-row key, retaining all43 accesses. -/
theorem padding_memory_keys {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) : PaddingMemoryKeys w := by
  exact MemoryKeyProofs.padding_keys accepted

/-- Equality before any division: no nonzero/inverse/compression-injectivity or
    native auxiliary, global memory/issuance/accounting enforcement is inferred. -/
theorem padding_memory_products {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) {w : Nat → ZMod mersenne31Modulus}
    (accepted : LocalProcessingAccepted w) : w constraintsABI.multiplicity = 0 →
    memoryKeyProduct embed ch w true = memoryKeyProduct embed ch w false := by
  exact MemoryKeyProofs.padding_products embed ch accepted

end Airbender.Blake2Worker.Native
