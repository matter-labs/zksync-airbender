import Airbender.Review.Circuits.ReducedMachine.MainAuxiliary
import Airbender.Review.Circuits.ReducedMachine.ConfiguredDelegation

namespace Airbender.ReducedMachine.NativeMainArguments
open Native NativeMainAuxiliary NativeMemoryBoundary Airbender.Blake2Worker

/-- One selected main observation: BOTH claims share the exact same body rows
    and typed auxiliary trace. The selected delegation-present normalized
    interface remains separate from Rust Option/ProofOutput/serialization and
    physical commitment/quotient extraction. No expected row/stream is supplied. -/
structure Proof (R : Type) [Field R] where
  memory : MainProof R
  polynomial : Polynomial R
  omega : R
  delegationClaim : R

def Proof.caller {R : Type} [Field R] (proof : Proof R) : CallerDelegationProof R :=
  ⟨proof.memory.rows,proof.memory.auxiliary,proof.polynomial,proof.omega,proof.delegationClaim⟩

def mainCallerSum {R : Type} [Field R] (proof : Proof R) : R := callerAuxiliarySum proof.caller

/-- Existing complete source-reference accepted components, now on the SAME
    main observations and SAME configured worker list/shared challenges. Every
    ordinary main and worker row, inactive factor and auxiliary value remains.
    Native accumulator checks, not desired matching/issued/result premises. -/
structure Accepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (config : Native.WorkerConfiguration Setup)
    (mains : List (Proof R)) (batch : Native.WorkerBatch Setup R) (inputs : PublicBoundary) (inverse : BoundaryInverses R) : Prop where
  mainMemory : ∀ proof ∈ mains, NativeMainAuxiliary.Accepted embed memory pc proof.memory
  mainDelegation : ∀ proof ∈ mains, CallerDelegationAccepted embed ch proof.caller
  globalMemory : UnifiedMemoryAccepted embed memory (workerProcessorChallenges ch) pc config
    (mains.map fun proof => proof.memory.grandClaim) batch inputs inverse
  delegationAccumulator : Native.statementDelegationAccumulator (mains.map Proof.delegationClaim)
    (batch.outputs.map Native.WorkerProofOutput.proof) = 0

/-- Simultaneous scalar/product/capacity conclusions, not token matching,
    initialized reads, cardinality equality, issuance or fulfillment. -/
structure Effects {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R) (pc : PCChallenges R)
    (mains : List (Proof R)) (batch : Native.WorkerBatch Setup R) (inputs : PublicBoundary) : Prop where
  delegation : (mains.map mainCallerSum).sum =
    ((batch.outputs.map Native.WorkerProofOutput.proof).map Native.workerAuxiliarySum).sum
  memory : registerProduct embed memory registerInitialKey * pcArgument embed pc initialPCKey *
      mainBatchProduct embed memory pc (mains.map Proof.memory) true * workerBatchProduct embed memory batch true =
    registerProduct embed memory (registerFinalKey inputs) * pcArgument embed pc (finalPCKey inputs) *
      mainBatchProduct embed memory pc (mains.map Proof.memory) false * workerBatchProduct embed memory batch false
  capacity : Native.batchActiveCount batch < mersenne31Modulus
  multiplicity : (Native.batchMultiplicitySum batch).val = Native.batchActiveCount batch

end Airbender.ReducedMachine.NativeMainArguments
