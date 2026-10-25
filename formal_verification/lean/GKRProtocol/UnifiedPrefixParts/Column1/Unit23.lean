import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source23 : Setup.Block := original.get ⟨23, by decide +kernel⟩

column_blocks_part part23_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 9 stop 10
noncomputable def destination23_0 : Setup.Block := part23_0.get ⟨0, by decide +kernel⟩

noncomputable def target23 : List Setup.Block := part23_0

theorem follows23 : blockTargetsFollow source23 0 target23 :=
  And.intro (by
    intro index bounded
    change source23.get? (0 + index) = destination23_0.get? index
    have same : source23 = destination23_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length23 : (target23.map Setup.Block.length).sum = source23.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
