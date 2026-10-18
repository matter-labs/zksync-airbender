import Airbender.Proofs.Trace.Families.WordMemory.SparseExecution

namespace Airbender.WordMemory
open Trace Reference.RiscV.Sail Verification
open _root_.Sail.ArchSem

/-- Successful sparse public construction and accepted complete native matching
    derive original fetched/decoded LW/SW execution and exact terminal PC/cells.
    Unsupported words retain their original slots; native rows cannot select them. -/
theorem sparse_public_sail_execution [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : SparseDecoderSetup WordMemoryFamily}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : sparseDecoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : SparseDecoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration initial)
    (image : wordROMImage initial romCount = some trace.rom) (programROM : count ≤ 1048576)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ seed ∈ seeds, seed.1.toNat < 4 * romCount) :
    WordMemory.Realizes setup.program trace initial cells :=
  Proofs.sparse_image_execution_soundness inputs decoder accepted decoded aligned configuration
    image programROM ordinary covered

end Airbender.WordMemory
