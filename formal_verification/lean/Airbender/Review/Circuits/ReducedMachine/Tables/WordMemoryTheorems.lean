import Airbender.Proofs.ReducedMachine.NativeWordMemoryTableValues

namespace Airbender.ReducedMachine.NativeFixed
set_option autoImplicit false

/-- Exact actual tag18 meaning over the complete native pool. -/
theorem word_offset_implementation {key bit0 bit1 : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,bit0,bit1,18]) :
    key.val < 65536 ∧ bit0 = (key.val%2 : Nat) ∧ bit1 = (key.val/2%2 : Nat) :=
  NativeWordMemoryTableValues.offset member

/-- Exact actual tag23 meaning; all loads retain the modulo-64 ROM shadow. -/
theorem word_separator_implementation {key ram shadow : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,ram,shadow,23]) :
    key.val < 65536 ∧ ram = ((if key.val < 64 then 0 else 1) : Nat) ∧
      shadow = (key.val%64 : Nat) := NativeWordMemoryTableValues.separator member

/-- Exact actual tag24 fixture and its complete repeated padding tail. This
    does not identify an arbitrary original public program with the native ROM. -/
theorem word_rom_implementation {key lo hi : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,lo,hi,24]) :
    key.val < 4194304 ∧ key.val%4 = 0 ∧
      #v[lo,hi] = (wordROMValue (key.val/4)).map Nat.cast :=
  NativeWordMemoryTableValues.rom member

end Airbender.ReducedMachine.NativeFixed
