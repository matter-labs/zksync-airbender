import Airbender.Proofs.Trace.Families.WordMemory.Composition

namespace Airbender.WordMemory.Proofs
open Trace Reference.RiscV.Sail Verification
open _root_.Sail.ArchSem

/-- Complete sparse membership derives selected entry evidence before calling
    the unchanged initialized history, original Sail row and terminal assembly.
    Physical holes/PCs stay in the public input table; only finite proof selection
    uses the supported entry list. No code bytes or instruction PCs are rewritten. -/
theorem sparse_image_execution_soundness [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : SparseDecoderSetup WordMemoryFamily}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : sparseDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : SparseDecoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration initial)
    (image : wordROMImage initial romCount = some trace.rom) (programROM : count ≤ 1048576)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ seed ∈ seeds, seed.1.toNat < 4 * romCount) :
    WordMemory.Realizes setup.program trace initial cells :=
  indexed_execution_soundness (setup := selectedSetup setup) inputs
    (sparse_indexed_program decoder) accepted (sparse_selected_decoded (by decide) accepted decoded)
    aligned configuration image programROM ordinary covered

end Airbender.WordMemory.Proofs
