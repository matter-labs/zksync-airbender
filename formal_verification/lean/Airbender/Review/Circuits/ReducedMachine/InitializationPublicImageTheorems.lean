import Airbender.Proofs.ReducedMachine.NativeInitializationPublicImage

namespace Airbender.NativeInitializationPublicImage
open Airbender.NativeInitializationBatch (Proof)
open Airbender.NativeInitializationSeedBoundary (terminalTokens accessTokens)
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Actual native seed coverage by ORIGINAL Sail reads in the explicit public
    reference constructor, retaining separate native ROM shadows. This adds no
    desired image/read premise and makes no arbitrary-state or physical claim. -/
theorem native_constructed_public_image {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse)
    (before : Reference.RiscV.Sail.State) : Effects proofs before :=
  NativeInitializationPublicImageProofs.public_image before (NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted)

/-- The same complete native memory ledger now starts from the derived original
    Sail image plus retained native shadows. Combined chronological memory and
    worker bounds/keys/accounting remain open. -/
theorem native_constructed_memory_matching {Setup R : Type} [Field R] (embed : F →+* R) (memory : MemoryKeyChallenges R)
    (ch : CSRArgumentChallenges R) (pc : PCChallenges R) (gamma : R) (config : WorkerConfiguration Setup)
    {proofs : List (Proof R)} {batch : WorkerBatch Setup R} {inputs : PublicBoundary} {inverse : BoundaryInverses R}
    (accepted : Airbender.NativeInitializationBatch.Accepted embed memory ch pc gamma config proofs batch inputs inverse) :
    (imageTokens proofs ++ accessTokens proofs batch true).Perm (terminalTokens proofs inputs ++ accessTokens proofs batch false) :=
  NativeInitializationPublicImageProofs.memory_matching (NativeInitializationSeedBoundaryProofs.boundary embed memory ch pc gamma config accepted) accepted.matching
end Airbender.NativeInitializationPublicImage
