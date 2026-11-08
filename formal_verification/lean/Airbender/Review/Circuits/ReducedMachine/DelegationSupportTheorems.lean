import Airbender.Proofs.ReducedMachine.NativeDelegationSupport

namespace Airbender.NativeDelegationSupport
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
open Airbender.ReducedMachine.NativeMemoryBoundary

/-- Conditional exact raw-key support from the same complete existing source
    component and the separately named formal crypto-extraction identity. -/
theorem native_worker_support {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : SourceIdentity proofs workers) : Anchored proofs workers :=
  NativeDelegationSupportProofs.anchored embed memory ch pc gamma config accepted identity

/-- Positive main count, every prefix guard, complete prior components and all
    rows remain. The transferred raw FIELD domain is not19bit chronology. -/
theorem native_counted_worker_support {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Anchored batch.proofs workers ∧ ClockDomains workers ∧ ReadDomains batch.proofs workers :=
  NativeDelegationSupportProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeDelegationSupport
