import Airbender.Review.Circuits.ReducedMachine.Scalar16LookupTheorems
import Tests.NativeScalar16Arguments

namespace Airbender.Tests.NativeScalar16Lookups
open Airbender.NativeScalar16Lookups Airbender.NativeScalar16LookupProofs
open Airbender.NativeScalar16Arguments Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
private abbrev csr := Airbender.ReducedMachine.NativeCSRPositiveWitness.assignment
private noncomputable def data : Proof F := Airbender.Tests.NativeScalar16Arguments.observed

/-- Observation DATA only; no complete main/aux/global/worker acceptance. -/
noncomputable def csrData (active : Bool) : Proof F :=
  ⟨⟨⟨fun _ => csr active,fun _ _ => 0,1⟩,fun _ _ => 0⟩,fun _ _ => 0,fun _ _ => 0,0,0⟩

private theorem zero_lookups {R : Type} [Field R] (proof : Proof R)
    (zero : ∀ i, ∀ pair : Fin 5, ∀ limb : Fin 2, query proof i pair limb = 0) : LogicalLookups proof := by
  intro i _ pair limb
  apply (Airbender.NativePhysicalScalar16SetupProofs.membership _).mpr
  rw [zero]
  decide

private theorem csr_queries (active : Bool) (i : Nat) (pair : Fin 5) (limb : Fin 2) :
    query (csrData active) i pair limb = 0 := by
  have independent : query (csrData active) i pair limb = query (csrData active) 0 pair limb := rfl
  rw [independent]
  cases active <;> fin_cases pair <;> fin_cases limb <;> decide +kernel

theorem actual_all_ten_queries : query data 0 0 0 = 61 ∧ query data 0 0 1 = 62 ∧
    query data 0 1 0 = 69 ∧ query data 0 1 1 = 70 ∧ query data 0 2 0 = 90 ∧ query data 0 2 1 = 91 ∧
    query data 0 3 0 = 122 ∧ query data 0 3 1 = 123 ∧ query data 0 4 0 = 126 ∧ query data 0 4 1 = 127 := by decide +kernel

/-- Complete existing BODY and ALL ordinary logical lookup rows. This is
    weaker than complete new source/global/physical acceptance, not an attack. -/
theorem complete_body_logical_lookups (active : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (csr active))
      (importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) ∧ LogicalLookups (csrData active) :=
  ⟨Airbender.ReducedMachine.NativeCSRPositiveWitness.body active,zero_lookups _ (csr_queries active)⟩

theorem inactive_request_retained : csr false 4 = 0 ∧ csr false 92 = 1 ∧ LogicalLookups (csrData false) :=
  ⟨by decide +kernel,by decide +kernel,(complete_body_logical_lookups false).2⟩

theorem conditional_all_query_bounds {R : Type} [Field R] {proof : Proof R} (lookups : LogicalLookups proof) :
    ∀ i < scalar16Layout.traceLength-1, ∀ pair : Fin 5, ∀ limb : Fin 2,
      (query proof i pair limb).val < 65536 := query_bounds lookups

theorem conditional_address_word {R : Type} [Field R] {proof : Proof R} (lookups : LogicalLookups proof)
    (i : Nat) (ordinary : i < scalar16Layout.traceLength-1) :
    (Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[0].val+
      65536*(Airbender.NativeInitializationOrdering.address (proof.initialization.main.rows i))[1].val < 4294967296 :=
  initialization_word_bound lookups i ordinary

theorem complete_conditional_component {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Proof R} (accepted : Airbender.NativeScalar16Lookups.Accepted embed memory pc gamma proof) :
    auxiliarySum proof true = auxiliarySum proof false ∧
      ∀ i < scalar16Layout.traceLength-1, ∀ pair : Fin 5, ∀ limb : Fin 2,
        (query proof i pair limb).val < 65536 := native_scalar16_constructed_lookups embed memory pc gamma accepted
end Airbender.Tests.NativeScalar16Lookups
