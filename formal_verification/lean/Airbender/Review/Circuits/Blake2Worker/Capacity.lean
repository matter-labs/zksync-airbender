import Airbender.Review.Circuits.Blake2Worker.Delegation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Airbender.Blake2Worker.Native

/-- Source-reference dispatch selects the corresponding monomorphic verifier.
    This label does not prove execution of either Rust function. -/
inductive WorkerSecurity where
  | security80 | security100
  deriving DecidableEq

/-- Selected configuration. Setup caps remain public configured data; their
    equality check is retained without identifying arbitrary caps with setup. -/
structure WorkerConfiguration (Setup : Type) where
  security : WorkerSecurity
  setupCaps : Setup

def configuredWorkerType : Nat := 1991
def configuredWorkerSlots : Nat := constraintsABI.traceLength-1

/-- Projections of returned native proof observations, separate from body and
    quartic columns. Physical ProofOutput/dispatch refinement remains open. -/
structure WorkerProofOutput (Setup R : Type) [Field R] where
  proof : DelegationProof R
  circuitSequence : Nat
  delegationType : Nat
  setupCaps : Setup
  memoryChallenges : MemoryKeyChallenges R
  delegationChallenges : ProcessorChallenges R

/-- The public stream supplies an unsigned32-bit proof count. All loop outputs
    are retained, including proofs with no multiplicity-one rows. -/
structure WorkerBatch (Setup R : Type) [Field R] where
  countWord : BitVec 32
  outputs : List (WorkerProofOutput Setup R)

def statementWorkerCapacity {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) : Nat :=
  batch.outputs.foldl (fun total _ => total+configuredWorkerSlots) 0

def workerActiveCount {R : Type} [Field R] (proof : DelegationProof R) : Nat :=
  ((Finset.range configuredWorkerSlots).filter fun i => proof.rows i constraintsABI.multiplicity = 1).card

def workerMultiplicitySum {R : Type} [Field R] (proof : DelegationProof R) : ZMod mersenne31Modulus :=
  ∑ i ∈ Finset.range configuredWorkerSlots, proof.rows i constraintsABI.multiplicity

def batchMultiplicitySum {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) : ZMod mersenne31Modulus :=
  (batch.outputs.map fun output => workerMultiplicitySum output.proof).sum

def batchActiveCount {Setup R : Type} [Field R] (batch : WorkerBatch Setup R) : Nat :=
  (batch.outputs.map fun output => workerActiveCount output.proof).sum

/-- Selected one-family component of the native unified verifier loop: actual
    count/metadata/shared-challenge checks, accepted normalized worker proofs,
    and the configured-slot counter's field bound. No issued count, expected
    stream, active flags, clock/read bounds or matching answers are supplied.
    Other configured families, transcript drawing and physical Rust acceptance
    are separate; this is not the whole verifier's acceptance proposition. -/
structure ConfiguredWorkersAccepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (config : WorkerConfiguration Setup)
    (batch : WorkerBatch Setup R) : Prop where
  count : batch.outputs.length = batch.countWord.toNat
  headers : ∀ output ∈ batch.outputs,
    output.circuitSequence = 0 ∧ output.delegationType = configuredWorkerType ∧
    output.setupCaps = config.setupCaps ∧ output.memoryChallenges = memory ∧
    output.delegationChallenges = processor
  proofs : ∀ output ∈ batch.outputs,
    DelegationAccepted embed output.memoryChallenges output.delegationChallenges output.proof
  capacity : statementWorkerCapacity batch < mersenne31Modulus

end Airbender.Blake2Worker.Native
