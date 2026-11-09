import Airbender.Review.Trace.Families.ReducedMachine.ScalarPairs
import Airbender.Review.Circuits.ReducedMachine.PhysicalScalar16Setup

namespace Airbender.NativeScalarTableCompletion
open Airbender.NativeInactiveMain Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native

def ScalarColumn (column : QuarticColumn) : Prop :=
  NativeScalarPairs.PairColumn column ∨ column = scalar16Layout.tableAccumulator

instance (column : QuarticColumn) : Decidable (ScalarColumn column) :=
  inferInstanceAs (Decidable (NativeScalarPairs.PairColumn column ∨ column = scalar16Layout.tableAccumulator))

def spike {R : Type} [Zero R] (value : R) (i : Nat) : R := if i = 0 then value else 0

def queryAmount : F := ((scalar16Layout.traceLength-1)*10 : Nat)

/-- A source-reference fixture for every challenge. At gamma0 the actual pair
    equations are poles; multiplicity0 retains that branch. This is not an
    honest-prover frequency-oracle or transcript refinement. -/
noncomputable def amount {R : Type} [Field R] (gamma : R) : F := by
  classical
  exact if gamma = 0 then 0 else queryAmount

def rawAuxiliary {R : Type} [Field R] (gamma value : R) (aux : QuarticColumn → R)
    (column : QuarticColumn) : R :=
  if column = scalar16Layout.tableAccumulator then value else NativeScalarPairs.pairAuxiliary gamma aux column

/-- Normalize exactly the five scalar pairs and scalar table column by the
    original negative actual ordinary sum. All other columns remain unchanged. -/
noncomputable def normalizedAuxiliary {R : Type} [Field R] (gamma : R) (base : MainProof R)
    (i : Nat) (column : QuarticColumn) : R :=
  if ScalarColumn column then Verification.normalizeLast scalar16Layout.traceLength
    (fun j => rawAuxiliary gamma (spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) j)
      (base.auxiliary j) column) i
  else rawAuxiliary gamma (spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) i)
    (base.auxiliary i) column

noncomputable def normalizedMemory {R : Type} [Field R] (gamma : R) (base : MainProof R) : MainProof R :=
  ⟨base.rows,normalizedAuxiliary gamma base,base.grandClaim⟩

/-- Same native main and typed products; construct only physical scalar witness7
    and setup0. No row-list or expected ledger equality is a premise. -/
noncomputable def scalarView {R : Type} [Field R] (gamma : R)
    (main : Airbender.ReducedMachine.NativeMainArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) (omega : R) :
    NativeScalar16Arguments.Proof R :=
  NativePhysicalScalar16Setup.withPublicSetup
    ⟨⟨main.memory,fun i => NativeScalarPairs.products (base i)⟩,
      (fun i column => if column.index = scalar16Layout.multiplicity.index then spike (amount gamma) i else witness i column),
      setup,polynomial,omega⟩
end Airbender.NativeScalarTableCompletion

namespace Airbender.NativeScalarTableCompletion
open Airbender.NativeInactiveMain Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMainAuxiliary Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker Airbender.Blake2Worker.Native

def rawDifference {R : Type} [Field R] (gamma : R) (i : Nat) : R :=
  spike (((scalar16Layout.traceLength-1 : Nat) : R)*(10/gamma)) i - 10/gamma

/-- Complete old same-main/caller/decoder/pair component and the complete scalar
    source family on that SAME main. Physical extraction and global statements
    are separate; neither sums nor expected samples are premises. -/
structure Completion {R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (pc : PCChallenges R) (ch : CSRArgumentChallenges R) (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (gamma : R) (w : Nat → F) (before : MainProof R) (omega : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) : Prop where
  paired : NativeScalarPairs.Completion embed memory pc ch decoder gamma w before omega proof base
  scalar : NativeScalar16Arguments.Accepted embed memory pc gamma
    (scalarView gamma proof.main base witness setup polynomial omega)

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
end Airbender.NativeScalarTableCompletion
