import Airbender.Proofs.SubwordMemory.Values

namespace Airbender.SubwordMemory
open Verification
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

theorem native_offset_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    OffsetValues w :=
  Proofs.accepted_offset_values holds

theorem native_rom_load_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : (w 20).val < 64) :
    ROMWordValues rom w ∧ LoadValues w (dataKey w (selectedLimb w 41 42)) :=
  Proofs.rom_load_values holds load range

theorem native_ram_load_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : 64 ≤ (w 20).val) :
    LoadValues w (dataKey w (selectedLimb w 32 33)) :=
  Proofs.ram_load_values holds load range

theorem native_store_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) : StoreValues w :=
  Proofs.store_values holds store

/-- Actual writes for either supported flag value; public decoder membership
    must still derive the flag before an architectural execution claim. -/
theorem native_load_write_cases
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) :
    (w 8 = 0 → #v[w 39,w 40] = #v[w 60,w 61]) ∧
    (w 8 = 1 → #v[w 39,w 40] = #v[0,0]) :=
  Proofs.load_write_cases holds load

end Airbender.SubwordMemory
