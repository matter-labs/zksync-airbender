import Airbender.Proofs.ReducedMachine.NativeMainBatch

namespace Airbender.NativeMainBatch
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Actual u32-counted source processed-capacity guards, not active requests. -/
theorem native_main_loop_capacity {R : Type} [Field R] (batch : Batch R)
    (accepted : CounterAccepted batch) : Effects batch := NativeMainBatchProofs.effects batch accepted

/-- Same count-indexed observations for complete existing acceptance and actual
    worker progress. Stream/ProofOutput/transcript/physical refinement is separate. -/
theorem native_counted_main_worker_progress {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Batch R} {workers : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : SourceAccepted embed memory ch pc gamma config batch workers inputs inverse) :
    Effects batch ∧ Airbender.NativeWorkerClockProgress.Effects workers :=
  NativeMainBatchProofs.joint embed memory ch pc gamma config accepted
end Airbender.NativeMainBatch
