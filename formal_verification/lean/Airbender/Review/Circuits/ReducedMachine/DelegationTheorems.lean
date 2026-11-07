import Airbender.Proofs.ReducedMachine.NativeCallerDelegation

namespace Airbender.ReducedMachine.Native

theorem caller_delegation_sum {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : CSRArgumentChallenges R) {proof : CallerDelegationProof R}
    (accepted : CallerDelegationAccepted embed ch proof) : callerAuxiliarySum proof = proof.delegationClaim :=
  NativeCallerDelegationProofs.caller_sum embed ch accepted

theorem caller_worker_rows_balance {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    {callers : List (CallerDelegationProof R)} {workers : List (Airbender.Blake2Worker.Native.DelegationProof R)}
    (accepted : CallerWorkerClaimsAccepted embed memory ch callers workers) :
    (callers.map callerAuxiliarySum).sum = (workers.map Airbender.Blake2Worker.Native.workerAuxiliarySum).sum :=
  NativeCallerDelegationProofs.rows_balance embed memory ch accepted

end Airbender.ReducedMachine.Native
