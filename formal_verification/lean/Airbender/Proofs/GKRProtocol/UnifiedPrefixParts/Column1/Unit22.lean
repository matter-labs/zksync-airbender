import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source22 : Setup.Block := original.get ⟨22, by decide +kernel⟩

column_blocks_part part22_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 8 stop 9
noncomputable def destination22_0 : Setup.Block := part22_0.get ⟨0, by decide +kernel⟩

noncomputable def target22 : List Setup.Block := part22_0

theorem follows22 : blockTargetsFollow source22 0 target22 :=
  And.intro (by
    intro index bounded
    change source22.get? (0 + index) = destination22_0.get? index
    have same : source22 = destination22_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length22 : (target22.map Setup.Block.length).sum = source22.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
