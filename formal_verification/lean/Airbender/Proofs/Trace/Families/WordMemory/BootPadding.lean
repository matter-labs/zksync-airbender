import Airbender.Proofs.Trace.Families.WordMemory.Boot
import Airbender.Proofs.Trace.PaddedSetup

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Verification
open _root_.Sail.ArchSem

/-- Explicit ROM padding preserves all fixed native seed/domain data and the
    original Sail zero profile. Shadow seeds still require no physical read. -/
theorem padded_native_boot_boundary {p : Nat} [Fact p.Prime]
    {trace : Data p WordMemoryFamily} {before : State} {cells : List Cell} {shadows : List (BitVec 32)}
    (inputs : NativeBootBoundary trace before cells shadows) {words : Nat} (bound : words ≤ 1048576) :
    NativeBootBoundary trace (paddedROMState before words) cells shadows :=
  ⟨inputs.domain, inputs.architectural, inputs.shadowsInROM,
    padded_rom_initial_profile inputs.profile bound, inputs.seed, inputs.initial⟩

/-- The public loader construction derives actual full-ROM extraction and all
    shadow coverage, while transporting existing setup/boot/configuration data. -/
theorem padded_boot_execution_soundness [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {before initial : State} {cells : List Cell} {shadows : List (BitVec 32)}
    {count logCapacity romCount : Nat}
    (inputs : NativeBootBoundary trace before cells shadows)
    (image : paddedWordROMImage before romCount = some (initial, trace.rom))
    (decoder : decoderSetupImage before count logCapacity = some setup) (code : count ≤ romCount)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (configuration : FlatMemoryConfiguration before)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address) :
    WordMemory.Realizes setup.program trace initial cells := by
  obtain ⟨prefixROM, source, rfl, padded⟩ := padded_image_source image
  have bound : romCount ≤ 1048576 := (rom_image_reads source).1 ▸ prefixROM.capacity
  have complete : wordROMImage (paddedROMState before romCount) 1048576 = some trace.rom := by
    rw [padded]
    exact padded_rom_image source
  exact native_boot_execution_soundness (padded_native_boot_boundary inputs bound)
    (padded_decoder_setup decoder code bound) accepted decoded aligned
    (padded_rom_configuration configuration romCount) complete (by omega) ordinary
    (fun address present => inputs.shadowsInROM address present)

end Airbender.WordMemory.Proofs
