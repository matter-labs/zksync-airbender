import Airbender.Proofs.Blake2Worker.NativeCapacity

namespace Airbender.Blake2Worker.Native

theorem configured_worker_capacity {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (config : WorkerConfiguration Setup)
    {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    batchActiveCount batch ≤ statementWorkerCapacity batch ∧
    batchActiveCount batch < mersenne31Modulus ∧ batch.outputs.length ≤ 2048 :=
  CapacityProofs.configured_bounds embed memory processor config accepted

theorem worker_multiplicity_count {R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) {proof : DelegationProof R}
    (accepted : DelegationAccepted embed memory processor proof) :
    workerMultiplicitySum proof = (workerActiveCount proof : ZMod mersenne31Modulus) :=
  CapacityProofs.multiplicity_count embed memory processor accepted

theorem configured_worker_multiplicity {Setup R : Type} [Field R]
    (embed : ZMod mersenne31Modulus →+* R) (memory : MemoryKeyChallenges R)
    (processor : ProcessorChallenges R) (config : WorkerConfiguration Setup)
    {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    (batchMultiplicitySum batch).val = batchActiveCount batch :=
  CapacityProofs.batch_multiplicity_no_wrap embed memory processor config accepted

end Airbender.Blake2Worker.Native
