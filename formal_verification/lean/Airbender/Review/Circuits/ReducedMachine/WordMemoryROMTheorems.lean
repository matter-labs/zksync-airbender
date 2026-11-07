import Airbender.Proofs.ReducedMachine.NativeWordMemoryROMRead

namespace Airbender.ReducedMachine.Native
open Verification Trace Reference.RiscV.Sail Arithmetic
set_option autoImplicit false

/-- Actual accepted LW constraints and the constructed original ROM bytes give
    the native fixed-ROM value at a ROM address. Ignored shadow values remain
    independent. Initialized projected row states, code frames, retained LOAD
    execution and physical preprocessing are separate obligations. -/
theorem word_load_rom_read (before : State) {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus))
    (region : (wordMemoryAddressWord w).hi < 64) :
    (Cell.ram (wordMemoryAddressWord w).toBitVec).read (NativeROM.state before) =
      .ok (⟨(w 66).val,(w 67).val⟩ : Word).toBitVec (NativeROM.state before) :=
  NativeWordMemoryROMProofs.rom_read before holds mask region

end Airbender.ReducedMachine.Native
