import Airbender.Proofs.ReducedMachine.NativeROMImage

namespace Airbender.ReducedMachine.Native
open Verification Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- Constructing the exact native fixture and complete UNIMP tail in original
    Sail bytes derives the full public extractor and every aligned ROM read.
    All registers and bytes outside ROM are preserved. No expected read, native
    table identity, shadow value, CSR configuration or physical-loader claim. -/
theorem public_rom_image (before : State) :
    wordROMImage (NativeROM.state before) 1048576 = some NativeROM.complete ∧
    (∀ i : Fin 1048576, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (NativeROM.state before) =
      .ok (wordMemoryROMWord i.val).toBitVec (NativeROM.state before)) ∧
    (NativeROM.state before).regs = before.regs ∧
    (∀ key, 4194304 ≤ key → (NativeROM.state before).mem[key]? = before.mem[key]?) :=
  ⟨NativeROMProofs.complete_image before, NativeROMProofs.numerical_read before,
    NativeROMProofs.registers before, fun _ outside => NativeROMProofs.outside_byte before outside⟩

end Airbender.ReducedMachine.Native
