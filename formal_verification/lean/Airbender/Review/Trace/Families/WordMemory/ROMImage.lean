import Airbender.Proofs.WordMemory.ROMImage
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory
open Arithmetic Trace Verification

/-- Native ROM data comes from actual original Sail bytes inside the extracted
    public prefix. Full native UNIMP padding is retained; its Sail-byte binding,
    discarded shadow accesses and instruction execution remain separate. -/
theorem public_rom_prefix_read {before : Reference.RiscV.Sail.State} {count : Nat}
    {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (image : wordROMImage before count = some rom)
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (region : (addressWord w).hi < 64) (within : (addressWord w).value < 4 * count) :
    (Cell.ram (addressWord w).toBitVec).read before =
      .ok (Word.mk (w 26).val (w 27).val).toBitVec before :=
  Proofs.native_rom_read (by decide) image native region within

end Airbender.WordMemory
