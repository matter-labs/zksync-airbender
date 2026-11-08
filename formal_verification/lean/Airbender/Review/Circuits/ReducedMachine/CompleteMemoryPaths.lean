import Airbender.Review.Circuits.ReducedMachine.StageTwoKeys

namespace Airbender.NativeCompleteMemoryPaths
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus

/-- Noninjective signed proof ordering only. Both raw timestamp fields remain
    in every token; this is not a native timestamp encoding or a Clean history. -/
def rank (token : Token) : Nat := (Airbender.NativeWorkerSignedClocks.value token.time).toNat

/-- One complete path for an actual seed address. Its adjacent edges are a
    permutation of ALL actual active ports at that address, retaining duplicates.
    Inactive ports stay in source acceptance and its full memory ledger. -/
structure AddressPath {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary)
    (source sink : Token) (path : List Token) : Prop where
  terminal : sink ∈ Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs
  address : sink.address = source.address
  first : path.head? = some source
  last : path.getLast? = some sink
  ordered : (path.map rank).Pairwise (· < ·)
  distinct : (path.map rank).Nodup
  ports : (path.zip path.tail).Perm ((Airbender.NativeMemoryRoots.steps proofs batch).filter
    fun edge => edge.1.address = source.address)

/-- Derived complete per-address paths, not a supplied history, unique global
    timestamps, initialized word-value bounds or worker/Sail reference results. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  keys : Airbender.NativeStageTwoKeys.Effects proofs batch inputs
  boundary : ((Airbender.NativeInitializationSeedBoundary.initialTokens proofs).map Trace.MemoryToken.address).Perm
    ((Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs).map Trace.MemoryToken.address)
  terminal : ((Airbender.NativeInitializationSeedBoundary.terminalTokens proofs inputs).map Trace.MemoryToken.address).Nodup
  paths : ∀ source ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs,
    ∃ sink path, AddressPath proofs batch inputs source sink path
  cover : ∀ read write, Airbender.NativeMixedMemoryOrder.Step proofs batch read write →
    ∃ source ∈ Airbender.NativeInitializationSeedBoundary.initialTokens proofs, ∃ sink path,
      AddressPath proofs batch inputs source sink path ∧ (read,write) ∈ path.zip path.tail
end Airbender.NativeCompleteMemoryPaths
