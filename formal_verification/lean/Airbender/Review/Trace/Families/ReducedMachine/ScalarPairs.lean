import Airbender.Review.Trace.Families.ReducedMachine.DecoderTableCompletion
import Airbender.Review.Circuits.ReducedMachine.Scalar16Arguments

namespace Airbender.NativeScalarPairs
open Airbender.NativeInactiveMain Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native

def PairColumn (column : QuarticColumn) : Prop :=
  column.start = 12 ∨ column.start = 16 ∨ column.start = 20 ∨ column.start = 24 ∨ column.start = 28

instance (column : QuarticColumn) : Decidable (PairColumn column) :=
  inferInstanceAs (Decidable (column.start = 12 ∨ column.start = 16 ∨ column.start = 20 ∨ column.start = 24 ∨ column.start = 28))

/-- The five actual pair accumulators. Other observations remain unchanged;
    these scalar pairs are not gated by execute. Reserved scalar normalization
    and the scalar table/sum polynomial are separate obligations. -/
def pairAuxiliary {R : Type} [Field R] (gamma : R) (aux : QuarticColumn → R) (column : QuarticColumn) : R :=
  if PairColumn column then 2/gamma else aux column

def pairMemory {R : Type} [Field R] (gamma : R) (base : MainProof R) : MainProof R :=
  ⟨base.rows,fun i => pairAuxiliary gamma (base.auxiliary i),base.grandClaim⟩

/-- Only typed BASE0..4 product oracles are constructed; these are not BODY
    variables, including execute4. All other base observations remain. -/
def products (base : BaseAuxiliaryColumn → F) (column : BaseAuxiliaryColumn) : F :=
  if column.index < 5 then 0 else base column

/-- Actual five scalar pair accumulator observations, separate from the table
    accumulator and from any issued delegation count. -/
def observedPairSum {R : Type} [Field R] (main : MainProof R) (i : Nat) : R :=
  (∑ slot : Fin 4, main.auxiliary i (Airbender.NativeScalar16Arguments.bodyAccumulator slot))+
    main.auxiliary i scalar16Layout.initializationAccumulator

/-- Complete same-main memory/caller/decoder components, all actual adjacent
    initialization ordering and all five ordinary scalar pair source relations.
    Scalar table/setup/difference polynomial and global source acceptance remain
    separate. No expected query, product, accumulator or sum is a premise. -/
structure Completion {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (gamma : R) (w : Nat → F) (before : MainProof R) (omega : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) : Prop where
  decoder : Airbender.NativeDecoderTableCompletion.Completion embed memory pc ch decoder w before omega proof
  initialization : Airbender.NativeInitializationRange.Accepted embed memory pc gamma
    ⟨proof.main.memory,fun i => products (base i)⟩
  bodyPairs : ∀ i < scalar16Layout.traceLength-1, ∀ slot : Fin 4,
    Airbender.NativeScalar16Arguments.BodyPairAccepted embed gamma (proof.main.memory.rows i)
      (products (base i)) (proof.main.memory.auxiliary i) slot

/-- Existential ordinary-pair component for every scalar challenge, retaining
    poles. This does not complete scalar table/sum/reserved normalization or a
    NONEMPTY full source/worker/physical witness. -/
def Fixture (w : Nat → F) : Prop :=
  w importedConstraintsTraceColumns.execute = 0 ∧ csrRequest w = ⟨1,1991,some 0,3⟩ ∧
  ∀ {Kind R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R),
    Nonpoles embed memory pc ch w → ∀ gamma omega, IsPrimitiveRoot omega callerAuxiliaryLayout.traceLength →
    ∀ (publicSetup : Trace.SparseDecoderSetup Kind) (witness : Nat → DecoderWitnessColumn → F)
      (setup : Nat → DecoderSetupColumn → F) (base : Nat → BaseAuxiliaryColumn → F), ∃ before main,
      Completion embed memory pc ch decoder gamma w before omega
        (Airbender.NativeDecoderTableCompletion.withPublicDecoder publicSetup main witness setup) base ∧
      main.delegationClaim = (8388607 : R)*(csrStageThreeArgument embed ch 1 w)⁻¹ ∧
      main.delegationClaim ≠ 0 ∧ ∀ constant, main.polynomial ≠ Polynomial.C constant
end Airbender.NativeScalarPairs
