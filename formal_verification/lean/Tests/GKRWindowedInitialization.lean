import Airbender.Proofs.GKRProtocol.WindowedPublic

namespace Tests.GKRWindowedInitialization
open Airbender Airbender.Compiler
set_option warningAsError true

def parameters (publicTops : Nat → Nat) : Initialization.Parameters babyBearModulus Source.BaseField :=
  ⟨RingHom.id _, 0, fun _ => 0, publicTops⟩

def reversedSparse : Nat → Nat := fun set => if set = 0 then 127 else 3

theorem reversed_sparse_windows_supported :
    Initialization.addressHi Initialization.unified.layout (parameters reversedSparse) 0 8388607 = 65535 ∧
    Initialization.addressHi Initialization.unified.layout (parameters reversedSparse) 1 8388607 = 2047 := by decide +kernel

theorem independent_window_changes_address :
    Initialization.addressHi Initialization.unified.layout (parameters (fun _ => 3)) 1 0 ≠
    Initialization.addressHi Initialization.unified.layout (parameters (fun _ => 4)) 1 0 := by decide +kernel

theorem top_bit_128_overflows_word :
    Initialization.addressHi Initialization.unified.layout (parameters (fun _ => 128)) 0 0 = 65536 := by decide +kernel

theorem virtual_high_has_no_public_window :
    8388607 / 16384 = 511 := by decide +kernel

end Tests.GKRWindowedInitialization
