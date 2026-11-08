import Airbender.Proofs.ReducedMachine.NativeCompleteMemoryPaths

namespace Airbender.NativeCompleteMemoryPaths
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary

/-- Complete ordered raw-token paths per actual seed address, covering all
    active main/worker port occurrences. Prior extraction stays explicit. -/
theorem native_complete_memory_paths {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeCompleteMemoryPathProofs.effects embed memory ch pc gamma config accepted identity

/-- Positive main count, every prefix guard and full prior acceptance stay
    coupled to these exact complete paths. Clean/Sail history stays separate. -/
theorem native_counted_complete_memory_paths {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeCompleteMemoryPathProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeCompleteMemoryPaths
