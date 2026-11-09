import Airbender.Review.Trace.Families.ReducedMachine.ScalarTableCompletion
import Airbender.Review.Circuits.ReducedMachine.InitializationWindow

namespace Airbender.NativeInitializationComponent
open Airbender.ReducedMachine.Native

/-- Public endpoint observations are constructed from the actual first and
    N-2 rows. The reserved N-1 row is not the native public endpoint. -/
def observedValues {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R) :
    NativeInitializationBoundary.PublicValues :=
  ⟨NativeInitializationBoundary.record (proof.initialization.main.rows 0),
    NativeInitializationBoundary.record (proof.initialization.main.rows (scalar16Layout.traceLength-2))⟩

def zeroValues : NativeInitializationBoundary.PublicValues :=
  ⟨Vector.replicate 6 0,Vector.replicate 6 0⟩

def chunk {R : Type} [Field R] (proof : NativeScalar16Arguments.Proof R) : NativeInitializationWindow.Chunk R :=
  ⟨proof,observedValues proof⟩
end Airbender.NativeInitializationComponent

namespace Airbender.NativeInitializationComponent
open Airbender.NativeInactiveMain Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native

/-- SAME full scalar/main/caller/decoder observation, its actually observed
    public endpoints and complete native initialization window components.
    Repeated positions remain indexed; this does not assert verifier counters,
    global matching/statements or any nonempty worker completion. -/
structure Completion {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (gamma : R) (w : Nat → F) (before : MainProof R) (omega : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) : Prop where
  source : NativeScalarTableCompletion.Completion embed memory pc ch decoder gamma w before omega proof base witness setup polynomial
  boundary : NativeInitializationBoundary.Accepted embed memory pc gamma
    (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup polynomial omega)
    (observedValues (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup polynomial omega))
  repeated : ∀ count, NativeInitializationWindow.Accepted embed memory pc gamma count
    (fun _ => chunk (NativeScalarTableCompletion.scalarView gamma proof.main base witness setup polynomial omega))
  padding : ∀ i < scalar16Layout.traceLength-1,
    NativeInitializationOrdering.PaddingRecord (proof.main.memory.rows i)

def Fixture (w : Nat → F) : Prop :=
  w importedConstraintsTraceColumns.execute = 0 ∧ csrRequest w = ⟨1,1991,some 0,3⟩ ∧
  ∀ {Kind R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R),
    Nonpoles embed memory pc ch w → ∀ gamma omega, IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength →
    ∀ (publicSetup : Trace.SparseDecoderSetup Kind) (decoderWitness : Nat → DecoderWitnessColumn → F)
      (decoderSetup : Nat → DecoderSetupColumn → F) (base : Nat → BaseAuxiliaryColumn → F)
      (witness : Nat → Scalar16WitnessColumn → F) (setup : Nat → Scalar16SetupColumn → F), ∃ before main polynomial,
      Completion embed memory pc ch decoder gamma w before omega
        (NativeDecoderTableCompletion.withPublicDecoder publicSetup main decoderWitness decoderSetup)
        base witness setup polynomial ∧
      main.delegationClaim = (8388607 : R)*(csrStageThreeArgument embed ch 1 w)⁻¹ ∧
      main.delegationClaim ≠ 0 ∧ ∀ constant, main.polynomial ≠ Polynomial.C constant
end Airbender.NativeInitializationComponent
