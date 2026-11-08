import Airbender.Review.Circuits.ReducedMachine.InitializationSeedBoundary
import Airbender.Review.Helpers.Memory.ReducedMachineInitialState

namespace Airbender.NativeInitializationPublicImage
open Airbender.NativeInitializationBatch (Proof)
open Airbender.NativeInitializationSeedBoundary (cells architecturalCells shadowSeeds)

/-- Actual successful architectural image and separate native shadow seeds, in
    partition order. Equality/permutation with the native ledger is derived. -/
def imageTokens {R : Type} [Field R] (proofs : List (Proof R)) : List (Trace.MemoryToken mersenne31Modulus) :=
  ((architecturalCells (cells proofs)).map fun cell => cell.initialToken 0) ++
    Airbender.ReducedMachine.NativeShadow.shadowTokens (shadowSeeds (cells proofs))

/-- Original Sail image coverage on the derived observed domain, for the explicit
    reference-input constructor. This is not arbitrary public-state coverage,
    alignment/platform permissions, initialized worker history or Rust extraction. -/
structure Effects {R : Type} [Field R] (proofs : List (Proof R))
    (before : Reference.RiscV.Sail.State) : Prop where
  observed : Airbender.NativeInitializationSeedBoundary.Effects proofs
  image : Trace.initialImage (p := mersenne31Modulus) (Airbender.ReducedMachine.NativeInitialState.state before)
    (architecturalCells (cells proofs)) = some ((architecturalCells (cells proofs)).map fun cell => cell.initialToken 0)
  shadowImage : Airbender.ReducedMachine.NativeShadow.shadowInitialImage
    (Airbender.ReducedMachine.NativeInitialState.state before) (architecturalCells (cells proofs)) (shadowSeeds (cells proofs)) =
      some (imageTokens proofs)
  initial : Trace.initialState (p := mersenne31Modulus) (Airbender.ReducedMachine.NativeInitialState.state before) (4,0) =
    some (PCState.boundary 0 (4,0))
  sameSeeds : (Airbender.NativeInitializationSeedBoundary.initialTokens proofs).Perm (imageTokens proofs)

end Airbender.NativeInitializationPublicImage
