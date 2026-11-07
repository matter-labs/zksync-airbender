import Airbender.Review.Circuits.ReducedMachine.AuxiliaryArtifact
import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePool
import Airbender.Review.Helpers.Memory.ReducedMachineCSRArgument
import Airbender.Review.Circuits.Blake2Worker.Delegation

namespace Airbender.ReducedMachine.Native
open Airbender.Blake2Worker

/-- Full ordinary native domain, including rows not selected as callers. This
    is separate from the existing active logical execution trace interface. -/
structure CallerDelegationProof (R : Type) [Field R] where
  rows : Nat → Nat → ZMod mersenne31Modulus
  auxiliary : Nat → QuarticColumn → R
  polynomial : Polynomial R
  omega : R
  delegationClaim : R

def callerAuxiliarySum {R : Type} [Field R] (proof : CallerDelegationProof R) : R :=
  ∑ i ∈ Finset.range (callerAuxiliaryLayout.traceLength-1), proof.auxiliary i callerAuxiliaryLayout.request

/-- Reviewed native individual caller relation, with scaling kept explicit. -/
def callerAuxiliaryTerm {R : Type} [Field R] (tau denominator multiplicity accumulator : R) : R :=
  tau*(denominator*accumulator-multiplicity)

/-- Complete original Clean body on the actual constructed runtime-CSR pool,
    each normalized native caller auxiliary relation, and its sum polynomial.
    No execute-one flag, CSR profile, stream, initialized read or desired sum is
    supplied for the full native domain. The caller denominator keeps the
    previously reviewed selected-constructor sequence0 normal form; it does not
    generalize that cache argument to other constructors or chunks. Physical
    refinement and global sequence dispatch remain separate. -/
structure CallerDelegationAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) (proof : CallerDelegationProof R) : Prop where
  body : ∀ i < callerAuxiliaryLayout.traceLength-1,
    FlatOperation.ConstraintsHoldFlat (Verification.environment (proof.rows i)) (importedConstraints NativeRuntimePool.table)
  auxiliary : ∀ i < callerAuxiliaryLayout.traceLength-1,
    callerAuxiliaryTerm 1 (csrStageThreeArgument embed ch 1 (proof.rows i))
      (embed (csrRequest (proof.rows i)).multiplicity) (proof.auxiliary i callerAuxiliaryLayout.request) = 0
  sumPolynomial : Airbender.Delegation.SumPolynomialAccepted callerAuxiliaryLayout.traceLength
    proof.omega proof.polynomial (fun i => proof.auxiliary i callerAuxiliaryLayout.request) proof.delegationClaim

def workerProcessorChallenges {R : Type} [Field R] (ch : CSRArgumentChallenges R) : Airbender.Blake2Worker.Native.ProcessorChallenges R :=
  ⟨ch.gamma,ch.abi,ch.low,ch.high⟩

/-- Native additive component with actual full main-row and selected worker
    auxiliary proofs. This supplies no issued ledger or expected worker stream. -/
structure CallerWorkerClaimsAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (callers : List (CallerDelegationProof R)) (workers : List (Airbender.Blake2Worker.Native.DelegationProof R)) : Prop where
  callerProofs : ∀ proof ∈ callers, CallerDelegationAccepted embed ch proof
  component : Airbender.Blake2Worker.Native.DelegationClaimsAccepted embed memory (workerProcessorChallenges ch)
    (callers.map CallerDelegationProof.delegationClaim) workers

end Airbender.ReducedMachine.Native
