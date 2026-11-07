import Airbender.Review.Circuits.Blake2Worker.CapacityTheorems
import Airbender.Review.Circuits.ReducedMachine.ConfiguredDelegationTheorems

namespace Airbender.Tests.NativeBlake2Capacity
open Verification Airbender.Blake2Worker Airbender.Blake2Worker.Native
set_option autoImplicit false

abbrev F := ZMod mersenne31Modulus

theorem actual_configuration : configuredWorkerType = 1991 ∧ configuredWorkerSlots = 1048575 := by decide +kernel

theorem exact_maximum_slots : 2048*configuredWorkerSlots = 2147481600 ∧
    2048*configuredWorkerSlots < mersenne31Modulus := by decide +kernel

theorem next_proof_exceeds_field : ¬ 2049*configuredWorkerSlots < mersenne31Modulus := by decide +kernel

theorem security_dispatch_distinct : WorkerSecurity.security80 ≠ WorkerSecurity.security100 := by decide +kernel

theorem u64_counter_headroom : (2^32-1)*configuredWorkerSlots < 2^64 := by decide +kernel

theorem counter_empty {Setup R : Type} [Field R] (word : BitVec 32) :
    statementWorkerCapacity (⟨word,[]⟩ : WorkerBatch Setup R) = 0 := rfl

theorem generic_indicator_positive :
    (∑ i ∈ Finset.range 4, (if i = 1 ∨ i = 3 then 1 else 0 : F)) = 2 := by decide +kernel

theorem nonboolean_is_not_indicator : (2 : F) ≠ (if (2 : F) = 1 then 1 else 0) := by decide +kernel

theorem rejected_sequence {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch)
    (output : WorkerProofOutput Setup R) (member : output ∈ batch.outputs) :
    output.circuitSequence ≠ 1 := by
  rw [(accepted.headers output member).1]
  decide

theorem retained_setup_and_challenges {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch)
    (output : WorkerProofOutput Setup R) (member : output ∈ batch.outputs) :
    output.delegationType = 1991 ∧ output.setupCaps = config.setupCaps ∧
      output.memoryChallenges = memory ∧ output.delegationChallenges = processor :=
  (accepted.headers output member).2

theorem complete_conditional_capacity {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    batchActiveCount batch ≤ statementWorkerCapacity batch ∧
      batchActiveCount batch < mersenne31Modulus ∧ batch.outputs.length ≤ 2048 :=
  configured_worker_capacity embed memory processor config accepted

theorem complete_conditional_multiplicity {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (processor : ProcessorChallenges R)
    (config : WorkerConfiguration Setup) {batch : WorkerBatch Setup R}
    (accepted : ConfiguredWorkersAccepted embed memory processor config batch) :
    (batchMultiplicitySum batch).val = batchActiveCount batch :=
  configured_worker_multiplicity embed memory processor config accepted

theorem count_word_counter {Setup R : Type} [Field R] (batch : WorkerBatch Setup R)
    (count : batch.outputs.length = batch.countWord.toNat) : statementWorkerCapacity batch < 2^64 :=
  CapacityProofs.counter_fits_u64 batch count

theorem complete_configured_caller_rows {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (ch : Airbender.ReducedMachine.Native.CSRArgumentChallenges R)
    (config : WorkerConfiguration Setup)
    {callers : List (Airbender.ReducedMachine.Native.CallerDelegationProof R)} {batch : WorkerBatch Setup R}
    (accepted : Airbender.ReducedMachine.Native.ConfiguredCallerWorkersAccepted embed memory ch config callers batch) :
    (callers.map Airbender.ReducedMachine.Native.callerAuxiliarySum).sum =
      ((batch.outputs.map WorkerProofOutput.proof).map workerAuxiliarySum).sum ∧
    batchActiveCount batch < mersenne31Modulus ∧
    (batchMultiplicitySum batch).val = batchActiveCount batch :=
  Airbender.ReducedMachine.Native.configured_caller_worker_rows embed memory ch config accepted

end Airbender.Tests.NativeBlake2Capacity
