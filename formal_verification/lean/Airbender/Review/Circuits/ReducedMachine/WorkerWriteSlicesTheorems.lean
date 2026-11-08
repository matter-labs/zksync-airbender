import Airbender.Proofs.ReducedMachine.NativeWorkerWriteSlices

namespace Airbender.NativeWorkerWriteSlices
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Verification

/-- Full BODY/queries derive bounded-or-copy observations at35 actual ports,
    retaining the eight still-open arithmetic ports and all raw timestamps. -/
theorem native_worker_write_slices {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w)
      (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerWriteSliceProofs.local_effects accepted

/-- Same complete counted source, prior extraction and latest reads; no input
    word bound, expected write, schedule or worker result is assumed. -/
theorem native_counted_worker_write_slices {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeWorkerWriteSliceProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeWorkerWriteSlices
