import Airbender.Proofs.ReducedMachine.NativeInitializationSeedBoundary

namespace Airbender.NativeInitializationSeedBoundary
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native

/-- Complete observed native GPR/RAM seed domain, zero clocks and exact shadow
    partition from SAME accepted arguments. Original Sail public image coverage,
    alignment/platform, combined history and physical extraction remain separate. -/
theorem native_complete_seed_boundary {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    Effects proofs := NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted

/-- Actual full memory-only matching: ALL32 public registers including x0 time,
    actual seed/teardown records, three active main ports and ALL43 worker ports.
    This supplies no initialized reads, worker clocks, keys or expected stream. -/
theorem native_complete_memory_matching {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    (initialTokens proofs ++ accessTokens proofs batch true).Perm
      (terminalTokens proofs inputs ++ accessTokens proofs batch false) :=
  NativeInitializationSeedBoundaryProofs.memory_matching accepted.matching
end Airbender.NativeInitializationSeedBoundary
