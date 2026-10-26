import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source25 : Setup.Block := original.get ⟨25, by decide +kernel⟩

column_blocks_part part25_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 11 stop 12
noncomputable def destination25_0 : Setup.Block := part25_0.get ⟨0, by decide +kernel⟩

noncomputable def target25 : List Setup.Block := part25_0

theorem follows25 : blockTargetsFollow source25 0 target25 :=
  And.intro (by
    intro index bounded
    change source25.get? (0 + index) = destination25_0.get? index
    have same : source25 = destination25_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length25 : (target25.map Setup.Block.length).sum = source25.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
