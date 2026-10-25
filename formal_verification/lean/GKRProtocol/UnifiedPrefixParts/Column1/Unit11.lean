import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source11 : Setup.Block := original.get ⟨11, by decide +kernel⟩

column_blocks_part part11_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 3 stop 4
noncomputable def destination11_0 : Setup.Block := part11_0.get ⟨0, by decide +kernel⟩

noncomputable def target11 : List Setup.Block := part11_0

theorem follows11 : blockTargetsFollow source11 0 target11 :=
  And.intro (by
    intro index bounded
    change source11.get? (0 + index) = destination11_0.get? index
    have same : source11 = destination11_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length11 : (target11.map Setup.Block.length).sum = source11.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
