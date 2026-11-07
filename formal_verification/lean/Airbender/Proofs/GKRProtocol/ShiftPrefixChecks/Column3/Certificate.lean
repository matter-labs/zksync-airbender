import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column3.Bindings

namespace Airbender.Compiler.ShiftPrefixChecks.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupNormalization
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem checked : PackedSetupNormalization.check requests = true := by decide +kernel

theorem facts (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound_at requests checked index

end Airbender.Compiler.ShiftPrefixChecks.Column3
