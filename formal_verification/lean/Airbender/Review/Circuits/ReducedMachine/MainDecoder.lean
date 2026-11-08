import Airbender.Review.Circuits.ReducedMachine.MainBatch
import Airbender.Review.Circuits.ReducedMachine.PhysicalDecoderSetup

namespace Airbender.NativeMainDecoder
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.Blake2Worker.Native Airbender.Trace
abbrev F := ZMod mersenne31Modulus

/-- One initialization/main proof plus separate typed decoder observations.
    Both argument views use its SAME main rows, auxiliaries and claims. Physical
    Rust/JSON column extraction between typed observations remains separate. -/
structure Proof (R : Type) [Field R] where
  initialization : Airbender.NativeInitializationBatch.Proof R
  witness : Nat → DecoderWitnessColumn → F
  setup : Nat → DecoderSetupColumn → F
  polynomial : Polynomial R
  omega : R

def Proof.decoder {R : Type} [Field R] (proof : Proof R) :
    Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R :=
  ⟨proof.initialization.main,proof.witness,proof.setup,proof.polynomial,proof.omega⟩

structure Batch (R : Type) [Field R] where
  countWord : BitVec 32
  outputs : Vector (Proof R) countWord.toNat

def Batch.proofs {R : Type} [Field R] (batch : Batch R) := batch.outputs.toList

def Batch.main {R : Type} [Field R] (batch : Batch R) : Airbender.NativeMainBatch.Batch R :=
  ⟨batch.countWord,batch.outputs.map Proof.initialization⟩

def Batch.decoder {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (batch : Batch R) :=
  batch.proofs.map fun proof => Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder

/-- Complete counted initialization/main/caller/worker/global components and all
    decoder access/table relations ON the constructed public decoder setup.
    Inactive rows, poles and physical tails remain. No expected row/list/query,
    source instruction, request stream or history equality is supplied. -/
structure SourceAccepted {Kind Setup R : Type} [Field R]
    (publicSetup : SparseDecoderSetup Kind) (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R)
    (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R)
    (config : WorkerConfiguration Setup) (batch : Batch R) (workers : WorkerBatch Setup R)
    (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  counted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch.main workers inputs inverse
  access : ∀ proof ∈ batch.proofs, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    Airbender.ReducedMachine.NativeDecoderArguments.RowAccepted embed decoder
      (proof.initialization.main.memory.rows i) (proof.initialization.main.memory.auxiliary i)
  tables : ∀ proof ∈ batch.proofs, Airbender.ReducedMachine.NativeDecoderTableArguments.TableAccepted embed decoder
    (Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder)

/-- Faithful logical extraction for actual execute-one queries. This is an
    EXPLICIT cryptographic boundary, not derived from fixed-challenge rational
    equations, sums, capacity, compression injectivity or a requested result. -/
def LogicalLookups {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind) (batch : Batch R) : Prop :=
  ∀ proof ∈ batch.proofs, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute = 1 →
      (Airbender.ReducedMachine.NativePhysicalDecoderSetup.table publicSetup).Contains #[]
        (decoderQuery (proof.initialization.main.memory.rows i))

structure DecoderEffects {Kind R : Type} [Field R] (publicSetup : SparseDecoderSetup Kind)
    (embed : F →+* R) (decoder : Airbender.ReducedMachine.NativeDecoderArguments.Challenges R) (batch : Batch R) : Prop where
  access : ∀ proof ∈ batch.proofs, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    Airbender.ReducedMachine.NativeDecoderArguments.argument embed decoder 1 (proof.initialization.main.memory.rows i) *
      proof.initialization.main.memory.auxiliary i decoderAuxiliaryLayout.access =
        embed (proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute)
  sums : ∀ proof ∈ batch.proofs,
    Airbender.ReducedMachine.NativeDecoderTableArguments.auxiliarySum proof.decoder true =
      Airbender.ReducedMachine.NativeDecoderTableArguments.auxiliarySum proof.decoder false
  zero : ∀ proof ∈ batch.proofs, proof.polynomial.eval 0 = 0
  last : ∀ proof ∈ batch.proofs,
    proof.initialization.main.memory.auxiliary (decoderTableLayout.traceLength-1) decoderTableLayout.tableMultiplicity =
      proof.initialization.main.memory.auxiliary (decoderTableLayout.traceLength-1) decoderTableLayout.access
  setup : ∀ proof ∈ batch.proofs, ∀ i < decoderTableLayout.traceLength-1,
    Airbender.ReducedMachine.NativeDecoderTableArguments.setupQuery
      (Airbender.ReducedMachine.NativePhysicalDecoderSetup.withPublicSetup publicSetup proof.decoder) i =
        Airbender.ReducedMachine.NativePhysicalDecoderSetup.ordinaryRow publicSetup i

/-- Original public byte read, stateful Sail decoder execution, projection and
    all ten query fields are conclusions. No delegated execution/retirement or
    all-request activity is asserted. -/
def PublicSources {Kind R : Type} [Field R]
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (publicSetup : SparseDecoderSetup Kind) (batch : Batch R) : Prop :=
  ∀ proof ∈ batch.proofs, ∀ i < decoderAuxiliaryLayout.traceLength-1,
    proof.initialization.main.memory.rows i importedConstraintsTraceColumns.execute = 1 →
      ∃ entry ∈ publicSetup.program, entry.SourceWith before projection ∧
        decoderQuery (proof.initialization.main.memory.rows i) = entry.query
end Airbender.NativeMainDecoder
