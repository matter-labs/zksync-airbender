import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source15 : Setup.Block := original.get ⟨15, by decide +kernel⟩

column_blocks_part part15_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination15_0 : Setup.Block := part15_0.get ⟨0, by decide +kernel⟩

noncomputable def target15 : List Setup.Block := part15_0

theorem follows15 : blockTargetsFollow source15 0 target15 :=
  And.intro (by
    intro index bounded
    change source15.get? (0 + index) = destination15_0.get? index
    have same : source15 = destination15_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length15 : (target15.map Setup.Block.length).sum = source15.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
