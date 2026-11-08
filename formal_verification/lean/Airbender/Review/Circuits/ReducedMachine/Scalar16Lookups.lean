import Airbender.Review.Circuits.ReducedMachine.PhysicalScalar16Setup

namespace Airbender.NativeScalar16Lookups
open Airbender.ReducedMachine.Native Airbender.NativeScalar16Arguments

/-- All TEN actual scalar-family values: four body pairs then initialization
    address126/127. No execute/opcode/worker filter is applied. -/
def query {R : Type} [Field R] (proof : Proof R) (i : Nat) (pair : Fin 5) (limb : Fin 2) : F :=
  if body : pair.val < 4 then (bodyPair (proof.initialization.main.rows i) ⟨pair.val,body⟩)[limb.val]
  else (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[limb.val]

/-- Explicit Clean-style native logical lookup boundary on EVERY actual family
    query and the CONSTRUCTED full ordinary table. This supplies no expected
    answer/range/stream/read/result. Extracting membership from fixed-challenge
    rational equations, polynomial sums or a physical proof remains unproved. -/
def LogicalLookups {R : Type} [Field R] (proof : Proof R) : Prop :=
  ∀ i < scalar16Layout.traceLength-1, ∀ pair : Fin 5, ∀ limb : Fin 2,
    Airbender.NativePhysicalScalar16Setup.table.Contains #[] #v[query proof i pair limb]

/-- Same complete normalized scalar16/main/init/ordering argument ON constructed
    public setup0, plus a separately named faithful logical lookup boundary.
    No acceptance is transferred from an arbitrary observed setup by equality.
    Physical setup authentication/quotient/cryptographic extraction is separate. -/
structure Accepted {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R)
    (gamma : R) (proof : Proof R) : Prop where
  arguments : Airbender.NativeScalar16Arguments.Accepted embed memory pc gamma
    (Airbender.NativePhysicalScalar16Setup.withPublicSetup proof)
  lookups : LogicalLookups proof
end Airbender.NativeScalar16Lookups
