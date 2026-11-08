import Airbender.Proofs.ReducedMachine.NativeInitializationBoundary

namespace Airbender.NativeInitializationBoundary
open Airbender.NativeInitializationOrdering Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Twelve native boundary polynomials bind ALL public endpoint fields and
    derive the actual sorted interval for EVERY ordinary record. Public image,
    chunk windows and initialized memory seeds are separate obligations. -/
theorem native_initialization_public_interval {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values) :
    record (proof.initialization.main.rows 0) = values.first ∧
    record (proof.initialization.main.rows (scalar16Layout.traceLength-2)) = values.oneBeforeLast ∧
    ∀ i < scalar16Layout.traceLength-1,
      addressValue values.first ≤ Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) ∧
      Airbender.NativeInitializationSorted.addressValue (proof.initialization.main.rows i) ≤ addressValue values.oneBeforeLast :=
  ⟨(NativeInitializationBoundaryProofs.full_endpoints embed memory pc gamma accepted).1,
    (NativeInitializationBoundaryProofs.full_endpoints embed memory pc gamma accepted).2,
    NativeInitializationBoundaryProofs.public_interval embed memory pc gamma accepted⟩

/-- Both PUBLIC address pairs inherit canonical16bit bounds from actual complete
    family lookup acceptance. Raw public teardown values/timestamps stay raw. -/
theorem native_initialization_public_bounds {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Accepted embed memory pc gamma proof values) :
    values.first[0].val < 65536 ∧ values.first[1].val < 65536 ∧
      values.oneBeforeLast[0].val < 65536 ∧ values.oneBeforeLast[1].val < 65536 :=
  NativeInitializationBoundaryProofs.public_bounds embed memory pc gamma accepted
end Airbender.NativeInitializationBoundary
