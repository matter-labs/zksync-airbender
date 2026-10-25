import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source26 : Setup.Block := original.get ⟨26, by decide +kernel⟩

column_blocks_part part26_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 12 stop 13
noncomputable def destination26_0 : Setup.Block := part26_0.get ⟨0, by decide +kernel⟩

noncomputable def target26 : List Setup.Block := part26_0

theorem follows26 : blockTargetsFollow source26 0 target26 :=
  And.intro (by
    intro index bounded
    change source26.get? (0 + index) = destination26_0.get? index
    have same : source26 = destination26_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26 : (target26.map Setup.Block.length).sum = source26.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
