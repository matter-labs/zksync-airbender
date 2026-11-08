import Airbender.Proofs.ReducedMachine.NativeScalar16Lookups

namespace Airbender.NativeScalar16Lookups
open Airbender.ReducedMachine.Native Airbender.NativeScalar16Arguments
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Under the explicit full-family native logical lookup boundary, BOTH actual
    initialization-address limbs are canonical16bit on EVERY ordinary row. -/
theorem native_initialization_address_bounds {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    ∀ i < scalar16Layout.traceLength-1,
      (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[0].val < 65536 ∧
      (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[1].val < 65536 :=
  NativeScalar16LookupProofs.initialization_bounds accepted.lookups

/-- Same constructed setup and same complete source component retain native
    scalar sum consistency AND derive all ten actual query bounds. Extraction
    of logical lookups from a physical proof remains a separate obligation. -/
theorem native_scalar16_constructed_lookups {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    auxiliarySum proof true = auxiliarySum proof false ∧
      ∀ i < scalar16Layout.traceLength-1, ∀ pair : Fin 5, ∀ limb : Fin 2,
        (query proof i pair limb).val < 65536 :=
  ⟨NativeScalar16LookupProofs.constructed_sum embed memory pc gamma accepted,
    NativeScalar16LookupProofs.query_bounds accepted.lookups⟩
end Airbender.NativeScalar16Lookups
