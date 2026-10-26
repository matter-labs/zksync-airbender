import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24 : Setup.Block := original.get ⟨24, by decide +kernel⟩

column_blocks_part part24_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 10 stop 11
noncomputable def destination24_0 : Setup.Block := part24_0.get ⟨0, by decide +kernel⟩

noncomputable def target24 : List Setup.Block := part24_0

theorem follows24 : blockTargetsFollow source24 0 target24 :=
  And.intro (by
    intro index bounded
    change source24.get? (0 + index) = destination24_0.get? index
    have same : source24 = destination24_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24 : (target24.map Setup.Block.length).sum = source24.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
