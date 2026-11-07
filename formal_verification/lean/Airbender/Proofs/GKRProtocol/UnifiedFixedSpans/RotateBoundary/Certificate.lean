import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Bindings

namespace Airbender.Compiler.UnifiedFixedSpans.RotateBoundary
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem checked : PackedSetupSpans.check requests = true := by decide +kernel

theorem facts : (Airbender.Compiler.UnifiedPrefixNative.Column1.target14.map Setup.Block.length).sum = Airbender.Compiler.UnifiedPrefixNative.Column1.source14.length ∧
    blockTargetsFollow Airbender.Compiler.UnifiedPrefixNative.Column1.source14 0 Airbender.Compiler.UnifiedPrefixNative.Column1.target14 := by
  rw [source_binding, targets_binding]
  exact PackedSetupSpans.check_sound_at requests checked ⟨0, by decide +kernel⟩

end Airbender.Compiler.UnifiedFixedSpans.RotateBoundary
