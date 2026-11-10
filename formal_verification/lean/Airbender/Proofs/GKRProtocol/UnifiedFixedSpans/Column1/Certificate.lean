import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column1.Bindings

namespace Airbender.Compiler.UnifiedFixedSpans.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem checked : PackedSetupSpans.check requests = true := by decide +kernel

end Airbender.Compiler.UnifiedFixedSpans.Column1
