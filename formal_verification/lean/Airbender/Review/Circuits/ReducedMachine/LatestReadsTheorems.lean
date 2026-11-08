import Airbender.Proofs.ReducedMachine.NativeLatestReads

namespace Airbender.NativeLatestReads
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary

/-- Exact latest old-read tokens among actual seeds and active writes in the
    derived proof order; both raw timestamp fields and extraction stay explicit. -/
theorem native_latest_reads {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeLatestReadsProofs.effects embed memory ch pc gamma config accepted identity

/-- Positive main count, every prefix guard and full prior acceptance stay
    coupled to these exact latest-read observations. Clean/Sail history stays separate. -/
theorem native_counted_latest_reads {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeLatestReadsProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeLatestReads
