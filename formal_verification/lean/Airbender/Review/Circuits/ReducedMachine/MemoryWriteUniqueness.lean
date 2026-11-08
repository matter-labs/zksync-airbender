import Airbender.Review.Circuits.ReducedMachine.CompleteMemoryPaths

namespace Airbender.NativeMemoryWriteUniqueness
open Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus
abbrev Token := Trace.MemoryToken mersenne31Modulus

/-- Address and noninjective proof rank, not a replacement raw memory key. -/
def writeKey (token : Token) : Nat × Nat :=
  (token.address,Airbender.NativeCompleteMemoryPaths.rank token)

/-- Consequences of complete actual paths. Simultaneous worker ports must have
    different raw addresses; this is derived, never a pointer-disjoint premise. -/
structure Effects {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (batch : WorkerBatch Setup R)
    (inputs : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary) : Prop where
  paths : Airbender.NativeCompleteMemoryPaths.Effects proofs batch inputs
  writes : ((Airbender.NativeMemoryRoots.steps proofs batch).map fun edge => writeKey edge.2).Nodup
  workerAddresses : ∀ w ∈ Airbender.NativeTokenLedger.workerRows batch,
    w constraintsABI.multiplicity = 1 → Function.Injective
      (fun slot : Fin 43 => (Airbender.NativeMemoryTokens.encodeKey (quotientMemoryKey w slot true)).address)
end Airbender.NativeMemoryWriteUniqueness
