import Airbender.Proofs.Trace.Families.WordMemory.Composition

namespace Airbender.WordMemory
open Trace Reference.RiscV.Sail Verification
open _root_.Sail.ArchSem

/-- Public initialization and accepted native constraints derive finite original
    Sail LW/SW execution, exact terminal PC and architectural terminal cells.
    Public configuration, ordinary RAM and actual ROM-prefix coverage are explicit;
    physical boot/export and cryptographic enforcement remain separate. -/
theorem public_sail_execution [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration initial)
    (image : wordROMImage initial romCount = some trace.rom) (programROM : count ≤ 1048576)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ seed ∈ seeds, seed.1.toNat < 4 * romCount) :
    WordMemory.Realizes setup.program trace initial cells :=
  Proofs.image_execution_soundness inputs decoder accepted decoded aligned configuration image programROM ordinary covered

end Airbender.WordMemory
