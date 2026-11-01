import Airbender.Proofs.GKRProtocol.SubwordRegionLengths.Column6.Bindings

namespace Airbender.Compiler.SubwordRegionLengths.Column6
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupLengths
set_option warningAsError true
set_option Elab.async false

theorem checked : PackedSetupLengths.check requests = true := by decide +kernel

theorem facts (index : Fin requests.length) : Fact (requests.get index) :=
  PackedSetupLengths.check_sound_at requests checked index

end Airbender.Compiler.SubwordRegionLengths.Column6
