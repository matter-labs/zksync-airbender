import Airbender.Proofs.ReducedMachine.NativeWorkerClockProgress

namespace Airbender.NativeWorkerClockProgress
open Airbender.Verification Airbender.Blake2Worker.Native
open Airbender.NativeInitializationBatch (Proof)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- Full native BODY derives a progress alternative; unbounded cases remain. -/
theorem native_worker_local_clock_progress {w : Nat → F}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Airbender.Blake2Worker.Fixed.table)) : LocalProgress w :=
  NativeWorkerClockProgressProofs.local_progress holds

/-- SAME complete native ledger derives strict bounded progress or an exact
    unbounded active source, including EVERY old read of an active zero clock.
    This does not exclude all zero clocks or establish initialized history. -/
theorem native_worker_clock_progress {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) : Effects batch :=
  NativeWorkerClockProgressProofs.effects embed memory ch pc gamma config accepted
end Airbender.NativeWorkerClockProgress
