import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source18 : Setup.Block := original.get ⟨18, by decide +kernel⟩

column_blocks_part part18_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 4 stop 5
noncomputable def destination18_0 : Setup.Block := part18_0.get ⟨0, by decide +kernel⟩

noncomputable def target18 : List Setup.Block := part18_0

theorem follows18 : blockTargetsFollow source18 0 target18 :=
  And.intro (by
    intro index bounded
    change source18.get? (0 + index) = destination18_0.get? index
    have same : source18 = destination18_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length18 : (target18.map Setup.Block.length).sum = source18.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
