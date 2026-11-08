import Airbender.Review.Circuits.ReducedMachine.Scalar16Lookups
import Airbender.Proofs.ReducedMachine.NativePhysicalScalar16Setup

namespace Airbender.NativeScalar16LookupProofs
open Airbender.NativeScalar16Lookups Airbender.NativeScalar16Arguments Airbender.ReducedMachine.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem body_query {R : Type} [Field R] (proof : Proof R) (i : Nat) (pair : Fin 4) (limb : Fin 2) :
    query proof i ⟨pair.val,by omega⟩ limb = (bodyPair (proof.initialization.main.rows i) pair)[limb.val] := by
  simp only [query,dif_pos pair.isLt]

theorem initialization_query {R : Type} [Field R] (proof : Proof R) (i : Nat) (limb : Fin 2) :
    query proof i 4 limb = (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[limb.val] :=
  dif_neg (by decide)

theorem constructed_queries {R : Type} [Field R] (proof : Proof R) (i : Nat) (pair : Fin 5) (limb : Fin 2) :
    query (Airbender.NativePhysicalScalar16Setup.withPublicSetup proof) i pair limb = query proof i pair limb := rfl

theorem query_bounds {R : Type} [Field R] {proof : Proof R} (lookups : LogicalLookups proof) :
    ∀ i < scalar16Layout.traceLength-1, ∀ pair : Fin 5, ∀ limb : Fin 2,
      (query proof i pair limb).val < 65536 := by
  intro i ordinary pair limb
  exact (Airbender.NativePhysicalScalar16SetupProofs.membership _).mp (lookups i ordinary pair limb)

theorem initialization_bounds {R : Type} [Field R] {proof : Proof R} (lookups : LogicalLookups proof) :
    ∀ i < scalar16Layout.traceLength-1,
      (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[0].val < 65536 ∧
      (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[1].val < 65536 := by
  intro i ordinary
  exact ⟨by simpa [initialization_query] using query_bounds lookups i ordinary 4 0,
    by simpa [initialization_query] using query_bounds lookups i ordinary 4 1⟩

theorem initialization_word_bound {R : Type} [Field R] {proof : Proof R} (lookups : LogicalLookups proof)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[0].val+
      65536*(Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[1].val < 4294967296 := by
  have bounds := initialization_bounds lookups i ordinary
  omega

theorem constructed_sum {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    auxiliarySum proof true = auxiliarySum proof false := by
  have h := Airbender.NativeScalar16ArgumentProofs.auxiliary_sum embed memory pc gamma accepted.arguments
  exact h
end Airbender.NativeScalar16LookupProofs
