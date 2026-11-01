import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column5.Bindings

namespace Airbender.Compiler.UnifiedFixedSpans.Column5
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem checked : PackedSetupSpans.check requests = true := by decide +kernel

theorem facts (index : Fin requests.length) : PackedSetupSpans.Fact (requests.get index) :=
  PackedSetupSpans.check_sound_at requests checked index

end Airbender.Compiler.UnifiedFixedSpans.Column5
