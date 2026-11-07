import Airbender.Proofs.ReducedMachine.NativeInitializationOrdering

namespace Airbender.NativeInitializationOrdering
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Adjacent repeated ACTUAL field addresses can only be zero padding. No
    address range, desired public seed or expected comparison flag is supplied. -/
theorem native_initialization_adjacent_repeats {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : NativeInitializationOrdering.Accepted embed memory pc proof) :
    ∀ i < callerAuxiliaryLayout.traceLength-2, address (proof.rows i) = address (proof.rows (i+1)) →
      PaddingRecord (proof.rows i) ∧ borrows (proof.rows i) = #v[0,0] ∧ remainder (proof.rows i) = #v[0,0] :=
  NativeInitializationOrderingProofs.full_domain_repeats embed memory pc accepted

/-- The same exclusion on the actual losslessly encoded native initialization
    token addresses. This does not infer global uniqueness or initialized reads. -/
theorem native_initialization_token_duplicates {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {proof : MainProof R}
    (accepted : NativeInitializationOrdering.Accepted embed memory pc proof)
    (i : Nat) (bound : i < callerAuxiliaryLayout.traceLength-2)
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey (proof.rows (i+1)) true)).address) :
    PaddingRecord (proof.rows i) :=
  (NativeInitializationOrderingProofs.full_domain_repeats embed memory pc accepted i bound
    (NativeInitializationOrderingProofs.token_address_binding same)).1

end Airbender.NativeInitializationOrdering
