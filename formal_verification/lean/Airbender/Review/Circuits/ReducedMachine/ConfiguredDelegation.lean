import Airbender.Review.Circuits.ReducedMachine.Delegation
import Airbender.Review.Circuits.Blake2Worker.Capacity

namespace Airbender.ReducedMachine.Native
open Airbender.Blake2Worker

/-- Selected native metadata/capacity and additive-claim components over the
    SAME returned worker list. Full caller rows and all worker rows are retained.
    No matching ledger, issued count or desired fulfillment stream is supplied. -/
structure ConfiguredCallerWorkersAccepted {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (config : Native.WorkerConfiguration Setup)
    (callers : List (CallerDelegationProof R)) (batch : Native.WorkerBatch Setup R) : Prop where
  callerProofs : ∀ caller ∈ callers, CallerDelegationAccepted embed ch caller
  workers : Native.ConfiguredWorkersAccepted embed memory (workerProcessorChallenges ch) config batch
  accumulator : Native.statementDelegationAccumulator
    (callers.map CallerDelegationProof.delegationClaim) (batch.outputs.map Native.WorkerProofOutput.proof) = 0

end Airbender.ReducedMachine.Native
