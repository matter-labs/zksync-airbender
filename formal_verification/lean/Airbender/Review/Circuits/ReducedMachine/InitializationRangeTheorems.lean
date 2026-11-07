import Airbender.Proofs.ReducedMachine.NativeInitializationRange

namespace Airbender.NativeInitializationRange
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.Blake2Worker.Native

/-- Exact ordinary-domain pair equations on the SAME complete native main
    proof. These are source equations, not an extracted lookup/range claim. -/
theorem native_initialization_address_pairs {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    ∀ i < initializationRangeLayout.traceLength-1,
      (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0])*
        (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1])*
        proof.main.auxiliary i initializationRangeLayout.accumulator =
      (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[0])+
        (gamma+embed (Airbender.NativeInitializationOrdering.address (proof.main.rows i))[1]) :=
  (NativeInitializationRangeProofs.full_domain embed memory pc gamma accepted).2

/-- Original repeated-record exclusion survives on the SAME stronger component;
    no range or expected ordering bit is added to obtain it. -/
theorem native_initialization_range_repeats {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Accepted embed memory pc gamma proof) :
    ∀ i < callerAuxiliaryLayout.traceLength-2,
      Airbender.NativeInitializationOrdering.address (proof.main.rows i) =
        Airbender.NativeInitializationOrdering.address (proof.main.rows (i+1)) →
      Airbender.NativeInitializationOrdering.PaddingRecord (proof.main.rows i) :=
  fun i bound same => (NativeInitializationOrderingProofs.full_domain_repeats embed memory pc accepted.ordering i bound same).1
end Airbender.NativeInitializationRange
