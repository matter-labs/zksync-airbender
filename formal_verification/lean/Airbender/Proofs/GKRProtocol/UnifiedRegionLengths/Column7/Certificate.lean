import Airbender.Proofs.GKRProtocol.UnifiedRegionLengths.Column7.Bindings

namespace Airbender.Compiler.UnifiedRegionLengths.Column7
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : PackedSetupLengths.check requests = true := by decide +kernel

theorem facts (index : Fin requests.length) : Fact (requests.get index) :=
  PackedSetupLengths.check_sound_at requests checked index

end Airbender.Compiler.UnifiedRegionLengths.Column7
