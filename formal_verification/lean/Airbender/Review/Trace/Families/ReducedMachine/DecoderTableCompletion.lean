import Airbender.Review.Trace.Families.ReducedMachine.CallerSumCompletion
import Airbender.Review.Circuits.ReducedMachine.PhysicalDecoderSetup

namespace Airbender.NativeDecoderTableCompletion
open Airbender.NativeInactiveMain Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native

/-- Construct only physical decoder multiplicity9 and setup6..15. All other
    physical witness/setup observations and the SAME complete main are retained.
    This is a source-reference construction, not a physical codec or commitment. -/
noncomputable def withPublicDecoder {Kind R : Type} [Field R] (publicSetup : Trace.SparseDecoderSetup Kind)
    (main : Airbender.ReducedMachine.NativeMainArguments.Proof R)
    (witness : Nat → DecoderWitnessColumn → F) (setup : Nat → DecoderSetupColumn → F) :
    Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R :=
  Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup
    ⟨main,(fun i column => if column = decoderTableLayout.multiplicity then 0 else witness i column),
      setup,0,main.omega⟩

/-- Both complete caller and decoder-table polynomial components on the SAME
    main observation. Scalar families, initialization ordering/boundaries and
    global statement/worker acceptance remain separate. -/
structure Completion {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (w : Nat → F) (base : MainProof R) (omega : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R) : Prop where
  caller : Airbender.NativeCallerSumCompletion.Completion embed memory pc ch decoder w base omega proof.main
  table : Airbender.ReducedMachine.NativeDecoderTableArguments.TableAccepted embed decoder proof

/-- An inactive request-positive component with a nonzero genuine caller claim,
    complete decoder-table equations and polynomial, and constructed public setup.
    Primitive-domain construction and full source/worker acceptance remain open. -/
def Fixture (w : Nat → F) : Prop :=
  w importedConstraintsTraceColumns.execute = 0 ∧ csrRequest w = ⟨1,1991,some 0,3⟩ ∧
  ∀ {Kind R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R),
    Nonpoles embed memory pc ch w → ∀ omega, IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength →
    ∀ (publicSetup : Trace.SparseDecoderSetup Kind) (witness : Nat → DecoderWitnessColumn → F)
      (setup : Nat → DecoderSetupColumn → F), ∃ base main,
      Completion embed memory pc ch decoder w base omega (withPublicDecoder publicSetup main witness setup) ∧
      main.delegationClaim = (8388607 : R)*(csrStageThreeArgument embed ch 1 w)⁻¹ ∧
      main.delegationClaim ≠ 0 ∧ ∀ constant, main.polynomial ≠ Polynomial.C constant
end Airbender.NativeDecoderTableCompletion
