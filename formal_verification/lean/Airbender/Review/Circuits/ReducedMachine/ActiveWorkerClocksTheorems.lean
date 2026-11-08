import Airbender.Proofs.ReducedMachine.NativeActiveWorkerClocks

namespace Airbender.NativeActiveWorkerClocks
open Airbender.NativeInitializationBatch (Proof)
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary

/-- On the SAME full native ledger, unbounded read clocks require an ACTUAL
    multiplicity1 worker write with that exact raw clock. No raw bound, request
    stream, clock progress, initialized history or worker-key result is assumed. -/
theorem native_active_worker_clock_sources {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs batch := NativeActiveWorkerClockProofs.read_clocks embed memory ch pc gamma config accepted
end Airbender.NativeActiveWorkerClocks
