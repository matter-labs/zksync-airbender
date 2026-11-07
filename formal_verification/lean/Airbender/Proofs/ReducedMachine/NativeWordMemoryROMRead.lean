import Airbender.Proofs.ReducedMachine.NativeROMImage
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDecodedResult

namespace Airbender.ReducedMachine.NativeWordMemoryROMProofs
open Native Arithmetic Verification Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- An actual accepted native ROM load reads the certified fixed-ROM output
    from original Sail bytes constructed from that fixture. The ignored second
    memory-port shadow value is not used or equated with these bytes. -/
theorem rom_read (before : State) {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus))
    (region : (wordMemoryAddressWord w).hi < 64) :
    (Cell.ram (wordMemoryAddressWord w).toBitVec).read (NativeROM.state before) =
      .ok (⟨(w 66).val,(w 67).val⟩ : Word).toBitVec (NativeROM.state before) := by
  have shape := NativeWordMemoryShapeProofs.load_address holds mask
  have bound : (wordMemoryAddressWord w).value < 4194304 := by
    have low := shape.1.1
    dsimp [Word.value,limbBase] at *
    omega
  have index : (wordMemoryAddressWord w).value/4 < 1048576 := by omega
  have read := NativeROMProofs.numerical_read before ⟨_,index⟩
  have address : BitVec.ofNat 32 (4*((wordMemoryAddressWord w).value/4)) =
      (wordMemoryAddressWord w).toBitVec := by
    have aligned : 4*((wordMemoryAddressWord w).value/4) = (wordMemoryAddressWord w).value := by
      have := shape.2.1
      omega
    exact congrArg (BitVec.ofNat 32) aligned
  rw [address] at read
  have value := NativeWordMemoryResultProofs.rom_word holds mask
  have key : ((w 61).val+65536*((w 62).val%64))/4 = (wordMemoryAddressWord w).value/4 := by
    change (w 62).val < 64 at region
    rw [Nat.mod_eq_of_lt region]
    rfl
  rw [key] at value
  rw [value]
  exact read

end Airbender.ReducedMachine.NativeWordMemoryROMProofs
