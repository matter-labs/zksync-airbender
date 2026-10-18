import Airbender.Proofs.WordMemory.PhysicalSetup

namespace Airbender.WordMemory
open Verification Trace Reference.RiscV.Sail

/-- Native-shaped physical setup membership, including tag 24 and every active
    dummy/padding row, binds actual ROM bytes after explicit loader construction.
    Rust row/export/LDE fidelity and cryptographic enforcement remain separate. -/
theorem physical_setup_rom_read {before initial : State} {rom : WordROM} {count : Nat}
    (image : paddedWordROMImage before count = some (initial, rom))
    {key lo hi : ZMod mersenne31Modulus}
    (member : NativeSetup.Contains rom 24 #v[key, lo, hi]) :
    (Cell.ram (BitVec.ofNat 32 key.val)).read initial =
      .ok (Arithmetic.Word.mk lo.val hi.val).toBitVec initial :=
  Proofs.padded_physical_rom_read image member

end Airbender.WordMemory
