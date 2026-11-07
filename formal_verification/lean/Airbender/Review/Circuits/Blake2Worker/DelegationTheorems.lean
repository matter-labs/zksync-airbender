import Airbender.Proofs.Blake2Worker.NativeDelegation

namespace Airbender.Blake2Worker.Native

theorem worker_delegation_sum {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {proof : DelegationProof R} (accepted : DelegationAccepted embed memory processor proof) :
    workerAuxiliarySum proof = proof.delegationClaim :=
  DelegationProofs.worker_sum embed memory processor accepted

theorem delegation_claims_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    {mains : List R} {proofs : List (DelegationProof R)}
    (accepted : DelegationClaimsAccepted embed memory processor mains proofs) :
    mains.sum = (proofs.map workerAuxiliarySum).sum :=
  DelegationProofs.claims_balance embed memory processor accepted

end Airbender.Blake2Worker.Native
