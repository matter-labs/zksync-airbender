import Airbender.Proofs.ReducedMachine.NativeMemoryHistory

namespace Airbender.NativeMemoryHistory
open Airbender.NativeInitializationBatch (Proof)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- ALL actual reads come from exact seed/main-write/worker-write tokens.
    A read clock outside the derived main/seed range requires an actual worker
    write source; nonempty-worker chronology is not assumed or inferred. -/
theorem native_actual_read_sources {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    ReadEffects proofs batch := NativeMemoryHistoryProofs.full_read_sources embed memory ch pc gamma config accepted

/-- Complete actual main-memory history when the selected worker batch is
    explicitly constructed empty. The same full native acceptance remains;
    caller requests are not filtered or assumed zero. This is Clean memory,
    separate from nonempty-worker/Sail instruction effects and physical fidelity. -/
theorem native_main_memory_history {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs (emptyWorkers Setup R) inputs inverse) :
    MainEffects proofs inputs := NativeMemoryHistoryProofs.main_history embed memory ch pc gamma config accepted
end Airbender.NativeMemoryHistory
