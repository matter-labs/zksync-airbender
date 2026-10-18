import Airbender.Proofs.Trace.Families.WordMemory.BootPadding

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

/-- Explicit proving-loader padding constructs Sail bytes and derives complete
    ROM coverage. Fixed native boot, actual public decoding and accepted matching
    yield original execution and exact terminal observables in the padded state.
    Rust export/refinement and argument enforcement remain separate. -/
theorem padded_boot_execution [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {before initial : State} {cells : List Cell} {shadows : List (BitVec 32)}
    {count logCapacity romCount : Nat}
    (inputs : NativeBootBoundary trace before cells shadows)
    (image : paddedWordROMImage before romCount = some (initial, trace.rom))
    (decoder : decoderSetupImage before count logCapacity = some setup) (code : count ≤ romCount)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration before)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address) :
    WordMemory.Realizes setup.program trace initial cells :=
  Proofs.padded_boot_execution_soundness inputs image decoder code accepted decoded aligned configuration ordinary

end Airbender.WordMemory
