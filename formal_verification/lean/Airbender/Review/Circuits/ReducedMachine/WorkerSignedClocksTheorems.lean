import Airbender.Proofs.ReducedMachine.NativeWorkerSignedClocks

namespace Airbender.NativeWorkerSignedClocks
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary

/-- Signed proof ordering is DERIVED on the same complete source and existing
    explicit formal extraction boundary. Raw tokens remain unchanged. -/
theorem native_worker_signed_progress {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers :=
  NativeWorkerSignedClockProofs.effects embed memory ch pc gamma config accepted identity

/-- Positive main count/all prefix guards/full prior components stay. Exact
    worker-only dependency cycles are excluded; seed reachability stays open. -/
theorem native_counted_worker_signed_progress {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers ∧ NoWorkerCycles workers :=
  NativeWorkerSignedClockProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeWorkerSignedClocks
