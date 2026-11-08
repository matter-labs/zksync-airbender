import Airbender.Proofs.ReducedMachine.NativeWorkerWriteWords

namespace Airbender.NativeWorkerWriteWords
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native
open Airbender.ReducedMachine.NativeMemoryBoundary Verification

/-- Full native BODY/queries derive bounded-or-copy writes at all43 actual
    ports. No input word bound, expected worker result or schedule is supplied. -/
theorem native_worker_write_words {w : Nat → F}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w)
      (constraints Airbender.Blake2Worker.Fixed.table)) : LocalEffects w :=
  NativeWorkerWriteWordProofs.local_effects accepted

/-- Same counted source, old explicit identity and prior exact latest reads.
    Copied old values still need initialized bounds in the combined induction. -/
theorem native_counted_worker_write_words {Setup R : Type} [Field R]
    (embed : F →+* R) (memory : MemoryKeyChallenges R) (ch : CSRArgumentChallenges R)
    (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {batch : Airbender.NativeMainBatch.Batch R} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeMainBatch.SourceAccepted embed memory ch pc gamma config batch workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity batch.proofs workers) :
    Airbender.NativeMainBatch.Effects batch ∧ Effects batch.proofs workers inputs :=
  NativeWorkerWriteWordProofs.counted embed memory ch pc gamma config accepted identity
end Airbender.NativeWorkerWriteWords
