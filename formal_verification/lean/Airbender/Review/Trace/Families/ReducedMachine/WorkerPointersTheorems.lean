import Airbender.Proofs.ReducedMachine.NativeWorkerPointers

namespace Airbender.NativeWorkerPointers
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMemoryBoundary
open Airbender.ReducedMachine.Native
open Airbender.NativeWorkerSnapshot
set_option autoImplicit false

/-- Complete initialized acceptance derives distinct actual pointer codes and
    exact MAIN origins for every nonzero pointer. At least one such MAIN write
    exists for EVERY active worker. No pointer/seed/read/history/activity/count/
    schedule result is supplied; this is not physical caller or Sail issuance. -/
theorem native_worker_pointer_origins {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Airbender.NativeInitializationBatch.Proof R)} {workers : WorkerBatch Setup R}
    {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs workers inputs inverse)
    (identity : Airbender.NativeDelegationSupport.SourceIdentity proofs workers)
    {w : Nat → F} (member : w ∈ Airbender.NativeTokenLedger.workerRows workers) (active : w constraintsABI.multiplicity = 1) :
    (read w 0).value ≠ (read w 25).value ∧
    (∀ pointer : Fin 2, (read w (pointerSlot pointer)).value ≠ 0 → MainOrigin proofs workers (read w (pointerSlot pointer))) ∧
    ∃ pointer : Fin 2, (read w (pointerSlot pointer)).value ≠ 0 ∧ MainOrigin proofs workers (read w (pointerSlot pointer)) :=
  NativeWorkerPointersProofs.effects embed memory ch pc gamma config accepted identity member active
end Airbender.NativeWorkerPointers
