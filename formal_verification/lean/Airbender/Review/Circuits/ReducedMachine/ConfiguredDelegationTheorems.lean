import Airbender.Proofs.ReducedMachine.NativeConfiguredDelegation

namespace Airbender.ReducedMachine.Native
open Airbender.Blake2Worker

theorem configured_caller_worker_rows {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (config : Native.WorkerConfiguration Setup)
    {callers : List (CallerDelegationProof R)} {batch : Native.WorkerBatch Setup R}
    (accepted : ConfiguredCallerWorkersAccepted embed memory ch config callers batch) :
    (callers.map callerAuxiliarySum).sum =
      ((batch.outputs.map Native.WorkerProofOutput.proof).map Native.workerAuxiliarySum).sum ∧
    Native.batchActiveCount batch < mersenne31Modulus ∧
    (Native.batchMultiplicitySum batch).val = Native.batchActiveCount batch :=
  NativeConfiguredDelegationProofs.bounded_rows_balance embed memory ch config accepted

end Airbender.ReducedMachine.Native
