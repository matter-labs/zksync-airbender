import Airbender.Review.Circuits.ReducedMachine.InitializationPublicImage
import Airbender.Proofs.ReducedMachine.NativeInitialState
import Airbender.Proofs.ReducedMachine.NativeInitializationSeedBoundary

namespace Airbender.NativeInitializationPublicImageProofs
open Airbender.NativeInitializationBatch (Proof)
open Airbender.NativeInitializationSeedBoundary (cells architecturalCells shadowSeeds initialTokens terminalTokens accessTokens)
open Airbender.NativeInitializationPublicImage
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Successful reads are derived for the actual observed architectural cells;
    no per-cell read, expected image or shadow/ROM-value equality is a premise. -/
theorem public_image {R : Type} [Field R] {proofs : List (Proof R)} (before : Reference.RiscV.Sail.State)
    (boundary : Airbender.NativeInitializationSeedBoundary.Effects proofs) : Effects proofs before := by
  have image := Airbender.ReducedMachine.NativeInitialStateProofs.architectural_image (p := mersenne31Modulus)
    before (architecturalCells (cells proofs)) boundary.architectural
  exact ⟨boundary,image,by simp only [Airbender.ReducedMachine.NativeShadow.shadowInitialImage,image,Option.map_some,imageTokens],
    Airbender.ReducedMachine.NativeInitialStateProofs.initial_pc before,boundary.partition⟩

/-- Partition order is transported by permutation, retaining every actual
    shadow, x0 timestamp and ALL43 worker ports. No trace/history is fabricated. -/
theorem memory_matching {Setup R : Type} [Field R] {proofs : List (Proof R)} {batch : WorkerBatch Setup R}
    {inputs : PublicBoundary} (boundary : Airbender.NativeInitializationSeedBoundary.Effects proofs)
    (matching : Airbender.NativeTokenLedger.LogicalMatching (Airbender.NativeInitializationBatch.mainProofs proofs) batch inputs) :
    (imageTokens proofs ++ accessTokens proofs batch true).Perm
      (terminalTokens proofs inputs ++ accessTokens proofs batch false) :=
  (List.Perm.append boundary.partition.symm (List.Perm.refl _)).trans
    (Airbender.NativeInitializationSeedBoundaryProofs.memory_matching matching)

end Airbender.NativeInitializationPublicImageProofs
