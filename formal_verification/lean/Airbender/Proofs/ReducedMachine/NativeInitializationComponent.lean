import Airbender.Proofs.ReducedMachine.NativeScalarTableCompletion
import Airbender.Proofs.ReducedMachine.NativeInitializationWindow
import Airbender.Proofs.ReducedMachine.NativeScalar16Lookups
import Airbender.Review.Trace.Families.ReducedMachine.InitializationComponent

namespace Airbender.NativeInitializationComponentProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.NativeInitializationComponent
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

/-- Idempotence of the existing constructor, not acceptance transfer from
    arbitrary setup observations. The calculation is generic before sampling. -/
theorem public_setup_idempotent {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R) :
    NativePhysicalScalar16Setup.withPublicSetup (NativePhysicalScalar16Setup.withPublicSetup proof) =
      NativePhysicalScalar16Setup.withPublicSetup proof := by
  cases proof
  unfold NativePhysicalScalar16Setup.withPublicSetup
  congr 1
  funext i column
  split_ifs <;> simp_all

theorem endpoint_self (w : Nat → F) :
    NativeInitializationBoundary.EndpointAccepted w (NativeInitializationBoundary.record w) := by
  intro slot
  simp [NativeInitializationBoundary.term]

theorem record_zero (active : Bool) : NativeInitializationBoundary.record
    (NativeCSRPositiveWitness.assignment active) = Vector.replicate 6 0 := by
  rw [(NativeInitializationBoundaryProofs.geometry _).1]
  cases active <;> decide +kernel

theorem query_zero {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R)
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false)
    (i : Nat) (pair : Fin 5) (limb : Fin 2) : NativeScalar16Lookups.query proof i pair limb = 0 := by
  unfold NativeScalar16Lookups.query
  split
  · rw [rows i,NativeScalarPairsProofs.body_pairs_zero]
    fin_cases limb <;> rfl
  · rw [rows i,(NativeScalarPairsProofs.initialization_zero false).1]
    fin_cases limb <;> rfl

theorem logical_lookups {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R)
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false) :
    NativeScalar16Lookups.LogicalLookups proof := by
  intro i _ pair limb
  rw [query_zero proof rows]
  exact (NativePhysicalScalar16SetupProofs.membership 0).mpr (by decide +kernel)

theorem observed_values_zero {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R)
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false) :
    observedValues proof = zeroValues := by
  unfold observedValues zeroValues
  rw [rows 0,rows (scalar16Layout.traceLength-2),record_zero false]

theorem window_zero : NativeInitializationWindow.WindowAccepted zeroValues zeroValues := by
  have parsed : NativeInitializationWindow.parseAddress (Vector.replicate 6 (0 : F)) = some 0 := by
    rw [NativeInitializationAddressParserProofs.parsed (by constructor <;> decide +kernel)]
    rfl
  simp [NativeInitializationWindow.WindowAccepted,zeroValues,parsed]

theorem boundary {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (gamma : R) (main : NativeMainArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (p : Polynomial R) (omega : R)
    (accepted : NativeScalar16Arguments.Accepted embed memory pc gamma
      (NativeScalarTableCompletion.scalarView gamma main base witness setup p omega))
    (rows : ∀ i,main.memory.rows i = NativeCSRPositiveWitness.assignment false) :
    NativeInitializationBoundary.Accepted embed memory pc gamma
      (NativeScalarTableCompletion.scalarView gamma main base witness setup p omega)
      (observedValues (NativeScalarTableCompletion.scalarView gamma main base witness setup p omega)) := by
  have same : NativePhysicalScalar16Setup.withPublicSetup
      (NativeScalarTableCompletion.scalarView gamma main base witness setup p omega) =
      NativeScalarTableCompletion.scalarView gamma main base witness setup p omega :=
    public_setup_idempotent _
  refine ⟨⟨?_,logical_lookups _ rows⟩,endpoint_self _,endpoint_self _⟩
  rw [same]
  exact accepted

theorem repeated {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (gamma : R) (proof : NativeScalar16Arguments.Proof R)
    (accepted : NativeInitializationBoundary.Accepted embed memory pc gamma proof (observedValues proof))
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false) (count : Nat) :
    NativeInitializationWindow.Accepted embed memory pc gamma count (fun _ => chunk proof) := by
  refine ⟨fun _ _ => accepted,?_⟩
  intro _ _
  change NativeInitializationWindow.WindowAccepted (observedValues proof) (observedValues proof)
  rw [observed_values_zero proof rows]
  exact window_zero

theorem padding {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (gamma : R) (proof : NativeScalar16Arguments.Proof R)
    (accepted : NativeInitializationBoundary.Accepted embed memory pc gamma proof (observedValues proof))
    (rows : ∀ i,proof.initialization.main.rows i = NativeCSRPositiveWitness.assignment false) :
    ∀ i < scalar16Layout.traceLength-1, NativeInitializationOrdering.PaddingRecord (proof.initialization.main.rows i) := by
  apply NativeInitializationWindowProofs.zero_terminal_padding embed memory pc gamma accepted
  rw [observed_values_zero proof rows]
  rfl
end Airbender.NativeInitializationComponentProofs

namespace Airbender.NativeInitializationComponentProofs
open Airbender.NativeInactiveMain Airbender.ReducedMachine Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native Airbender.NativeInitializationComponent
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem original_fixture : NativeInitializationComponent.Fixture (NativeCSRPositiveWitness.assignment false) := by
  obtain ⟨inactive,request,old⟩ := NativeScalarTableCompletionProofs.original_fixture
  refine ⟨inactive,request,?_⟩
  intro Kind R _ embed memory pc ch decoder nonpoles gamma omega primitive publicSetup decoderWitness decoderSetup base witness setup
  obtain ⟨before,main,p,source,claim,nonzero,nonconstant⟩ := old embed memory pc ch decoder nonpoles gamma omega primitive
    publicSetup decoderWitness decoderSetup base witness setup
  have rows : ∀ i, main.memory.rows i = NativeCSRPositiveWitness.assignment false := by
    intro i
    simpa only [NativeDecoderTableCompletionProofs.same_main] using
      congrFun source.paired.decoder.caller.components.1 i
  have scalar : NativeScalar16Arguments.Accepted embed memory pc gamma
      (NativeScalarTableCompletion.scalarView gamma main base witness setup p omega) := by
    simpa only [NativeDecoderTableCompletionProofs.same_main] using source.scalar
  have endpoints := boundary embed memory pc gamma main base witness setup p omega scalar rows
  have windows := repeated embed memory pc gamma _ endpoints rows
  have allPadding := padding embed memory pc gamma _ endpoints rows
  refine ⟨before,main,p,⟨source,?_,?_,?_⟩,claim,nonzero,nonconstant⟩
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using endpoints
  · simpa only [NativeDecoderTableCompletionProofs.same_main] using windows
  · simpa only [NativeDecoderTableCompletionProofs.same_main,NativeScalarTableCompletion.scalarView,NativePhysicalScalar16Setup.withPublicSetup] using allPadding

theorem fixture : ∃ w, NativeInitializationComponent.Fixture w :=
  ⟨NativeCSRPositiveWitness.assignment false,original_fixture⟩
end Airbender.NativeInitializationComponentProofs
