import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source12 : Setup.Block := original.get ⟨12, by decide +kernel⟩

column_blocks_part part12_0 from (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination12_0 : Setup.Block := part12_0.get ⟨0, by decide +kernel⟩

noncomputable def target12 : List Setup.Block := part12_0

theorem follows12 : blockTargetsFollow source12 0 target12 :=
  And.intro (by
    intro index bounded
    change source12.get? (0 + index) = destination12_0.get? index
    have same : source12 = destination12_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length12 : (target12.map Setup.Block.length).sum = source12.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
