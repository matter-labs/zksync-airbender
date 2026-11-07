import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Certificate

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

theorem follows14 : blockTargetsFollow source14 0 target14 := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.facts.2

theorem length14 : (target14.map Setup.Block.length).sum = source14.length := Airbender.Compiler.UnifiedFixedSpans.RotateBoundary.facts.1

end Airbender.Compiler.UnifiedPrefixNative.Column1
