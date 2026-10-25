import GKRProtocol.InitializationPublic

namespace Tests.GKRInitializationTokens
open Airbender Airbender.Compiler
set_option warningAsError true

def parameters : Initialization.Parameters babyBearModulus Source.BaseField :=
  ⟨RingHom.id _, 0, fun _ => 0, fun set => 126 + set⟩

theorem final_inline_address_is_bounded :
    Initialization.addressHi Initialization.unified.layout parameters 1 8388607 = 65535 := by decide +kernel

theorem next_inline_window_overflows_word :
    65536 ≤ Initialization.addressHi Initialization.unified.layout
      {parameters with windows := fun set => 127 + set} 1 8388607 := by decide +kernel

theorem low_address_keeps_word_alignment : Initialization.addressLo 8388607 = 65532 := by decide +kernel

end Tests.GKRInitializationTokens
