import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source20 : Setup.Block := original.get ⟨20, by decide +kernel⟩

column_blocks_part part20_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 6 stop 7
noncomputable def destination20_0 : Setup.Block := part20_0.get ⟨0, by decide +kernel⟩

noncomputable def target20 : List Setup.Block := part20_0

theorem follows20 : blockTargetsFollow source20 0 target20 :=
  And.intro (by
    intro index bounded
    change source20.get? (0 + index) = destination20_0.get? index
    have same : source20 = destination20_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length20 : (target20.map Setup.Block.length).sum = source20.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
