import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source8 : Setup.Block := original.get ⟨8, by decide +kernel⟩

column_blocks_part part8_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination8_0 : Setup.Block := part8_0.get ⟨0, by decide +kernel⟩

noncomputable def target8 : List Setup.Block := part8_0

theorem follows8 : blockTargetsFollow source8 0 target8 :=
  And.intro (by
    intro index bounded
    change source8.get? (0 + index) = destination8_0.get? index
    have same : source8 = destination8_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length8 : (target8.map Setup.Block.length).sum = source8.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
