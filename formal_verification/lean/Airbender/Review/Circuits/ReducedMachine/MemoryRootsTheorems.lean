import Airbender.Proofs.ReducedMachine.NativeMemoryRoots

namespace Airbender.NativeMemoryRoots
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary

/-- Exact inactive-token cancellation and actual seed paths for active main
    and worker ports. Prior formal crypto extraction stays explicit. -/
theorem native_memory_seed_paths {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers) : Effects proofs workers inputs :=
  NativeMemoryRootsProofs.effects embed memory ch pc gamma config accepted identity

/-- Positive main count, every prefix guard and full prior acceptance stay
    coupled to these same seed paths; no online history or Sail claim is made. -/
theorem native_counted_memory_seed_paths {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeMemoryRootsProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeMemoryRoots
