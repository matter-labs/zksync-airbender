import Airbender.Review.Circuits.Blake2Worker.Auxiliary
import Airbender.Review.Helpers.Memory.DelegationSum

namespace Airbender.Blake2Worker.Native
open AuxiliaryArtifact

/-- Returned native worker proof data, with the auxiliary trace kept separate
    from the body variables. Claims are observables, not expected worker results. -/
structure DelegationProof (R : Type) [Field R] where
  rows : Nat → Nat → ZMod mersenne31Modulus
  auxiliary : Nat → QuarticColumn → R
  polynomial : Polynomial R
  omega : R
  memoryClaim : R
  delegationClaim : R

def workerAuxiliarySum {R : Type} [Field R] (proof : DelegationProof R) : R :=
  ∑ i ∈ Finset.range (constraintsABI.traceLength-1), proof.auxiliary i auxiliaryLayout.processing

/-- Complete previous native body/processing/memory acceptance and the additional
    reviewed sum-divisor relation with actual samples and degree/domain bounds.
    Physical interpolation, quotient and verifier refinement stay separate. -/
structure DelegationAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R) (proof : DelegationProof R) : Prop where
  trace : AuxiliaryTraceAccepted embed memory processor proof.rows proof.auxiliary proof.memoryClaim
  sumPolynomial : Airbender.Delegation.SumPolynomialAccepted constraintsABI.traceLength proof.omega proof.polynomial
    (fun i => proof.auxiliary i auxiliaryLayout.processing) proof.delegationClaim

/-- Exact additive component of the native unified statement: add each main
    returned claim, then subtract every worker returned claim, starting at0.
    Main claims are still opaque proof observables, not identified caller sums. -/
def statementDelegationAccumulator {R : Type} [Field R] (mainClaims : List R) (workers : List (DelegationProof R)) : R :=
  workers.foldl (fun accumulator proof => accumulator-proof.delegationClaim)
    (mainClaims.foldl (·+·) 0)

/-- Selected-worker scalar component only. This is not complete verifier
    acceptance, a claimed issued ledger, multiset equality or cardinality bound. -/
structure DelegationClaimsAccepted {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (mainClaims : List R) (workers : List (DelegationProof R)) : Prop where
  proofs : ∀ proof ∈ workers, DelegationAccepted embed memory processor proof
  accumulator : statementDelegationAccumulator mainClaims workers = 0

end Airbender.Blake2Worker.Native
