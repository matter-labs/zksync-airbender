import Airbender.Review.Circuits.ReducedMachine.ConfiguredDelegation
import Airbender.Proofs.ReducedMachine.NativeCallerDelegation
import Airbender.Proofs.Blake2Worker.NativeCapacity

namespace Airbender.ReducedMachine.NativeConfiguredDelegationProofs
open Native Airbender.Blake2Worker
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem claims_acceptance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (config : Native.WorkerConfiguration Setup)
    {callers : List (CallerDelegationProof R)} {batch : Native.WorkerBatch Setup R}
    (accepted : ConfiguredCallerWorkersAccepted embed memory ch config callers batch) :
    CallerWorkerClaimsAccepted embed memory ch callers (batch.outputs.map Native.WorkerProofOutput.proof) := by
  refine ⟨accepted.callerProofs,⟨?_,accepted.accumulator⟩⟩
  intro proof member
  obtain ⟨output,origin,rfl⟩ := List.mem_map.mp member
  exact CapacityProofs.shared_acceptance embed memory (workerProcessorChallenges ch) config accepted.workers output origin

theorem bounded_rows_balance {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : Native.MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (config : Native.WorkerConfiguration Setup)
    {callers : List (CallerDelegationProof R)} {batch : Native.WorkerBatch Setup R}
    (accepted : ConfiguredCallerWorkersAccepted embed memory ch config callers batch) :
    (callers.map callerAuxiliarySum).sum =
      ((batch.outputs.map Native.WorkerProofOutput.proof).map Native.workerAuxiliarySum).sum ∧
    Native.batchActiveCount batch < mersenne31Modulus ∧
    (Native.batchMultiplicitySum batch).val = Native.batchActiveCount batch := by
  exact ⟨NativeCallerDelegationProofs.rows_balance embed memory ch
      (claims_acceptance embed memory ch config accepted),
    (CapacityProofs.configured_bounds embed memory (workerProcessorChallenges ch) config accepted.workers).2.1,
    CapacityProofs.batch_multiplicity_no_wrap embed memory (workerProcessorChallenges ch) config accepted.workers⟩

end Airbender.ReducedMachine.NativeConfiguredDelegationProofs
