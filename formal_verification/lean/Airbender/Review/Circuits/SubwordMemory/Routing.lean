import Airbender.Proofs.SubwordMemory.Routing

namespace Airbender.SubwordMemory
open Verification
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

theorem native_operation_modes
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
     : ModeRouting w :=
  Proofs.mode_routing holds

theorem native_rom_load_routing
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : (w 20).val < 64) : ROMLoadRouting rom w :=
  Proofs.rom_load_routing holds load range

theorem native_ram_load_routing
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : 64 ≤ (w 20).val) : RAMLoadRouting w :=
  Proofs.ram_load_routing holds load range

theorem native_store_routing
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) : StoreRouting w :=
  Proofs.store_routing holds store

end Airbender.SubwordMemory
