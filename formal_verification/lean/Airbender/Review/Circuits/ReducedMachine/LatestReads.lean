import Airbender.Review.Circuits.ReducedMachine.MemoryWriteUniqueness

namespace Airbender.NativeLatestReads
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus

/-- Exact initialized tokens and all actual active writes, with every copy. -/
def available {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R) :=
  Airbender.NativeInitializationSeedBoundary.initialTokens proofs ++
    (Airbender.NativeMemoryRoots.steps proofs batch).map Prod.snd

/-- Latest reads in the derived proof order. Both raw timestamp fields and
    values remain exact; this does not recode clocks or assert a Clean history. -/
structure Latest {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (read write : Token) : Prop where
  source : read ∈ available proofs batch
  before : Airbender.NativeCompleteMemoryPaths.rank read < Airbender.NativeCompleteMemoryPaths.rank write
  latest : ∀ candidate ∈ available proofs batch, candidate.address = read.address →
    Airbender.NativeCompleteMemoryPaths.rank candidate < Airbender.NativeCompleteMemoryPaths.rank write →
    Airbender.NativeCompleteMemoryPaths.rank candidate ≤ Airbender.NativeCompleteMemoryPaths.rank read
  exact : ∀ candidate ∈ available proofs batch, candidate.address = read.address →
    Airbender.NativeCompleteMemoryPaths.rank candidate = Airbender.NativeCompleteMemoryPaths.rank read → candidate = read

structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  unique : Airbender.NativeMemoryWriteUniqueness.Effects proofs batch inputs
  reads : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write → Latest proofs batch read write
end Airbender.NativeLatestReads
