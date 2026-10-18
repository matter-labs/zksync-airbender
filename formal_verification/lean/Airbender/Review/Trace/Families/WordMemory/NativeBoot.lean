import Airbender.Proofs.Trace.Families.WordMemory.Boot

namespace Airbender.WordMemory
open Trace Reference.RiscV.Sail Verification
open _root_.Sail.ArchSem

/-- Fixed native zero boot and the original Sail initial profile derive the
    existing initialized execution boundary. Exact terminal PC and architectural
    cells follow; native shadows remain separate from actual ROM bytes.
    Padding, Rust export/refinement and argument enforcement remain separate. -/
theorem native_boot_execution [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial : State} {cells : List Cell} {shadows : List (BitVec 32)} {count logCapacity romCount : Nat}
    (inputs : NativeBootBoundary trace initial cells shadows)
    (decoder : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration initial)
    (image : wordROMImage initial romCount = some trace.rom) (programROM : count ≤ 1048576)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ address ∈ shadows, address.toNat < 4 * romCount) :
    WordMemory.Realizes setup.program trace initial cells :=
  Proofs.native_boot_execution_soundness inputs decoder accepted decoded aligned configuration image programROM ordinary covered

end Airbender.WordMemory
