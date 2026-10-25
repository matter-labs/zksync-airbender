import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source16 : Setup.Block := original.get ⟨16, by decide +kernel⟩

column_blocks_part part16_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination16_0 : Setup.Block := part16_0.get ⟨0, by decide +kernel⟩

noncomputable def target16 : List Setup.Block := part16_0

theorem follows16 : blockTargetsFollow source16 0 target16 :=
  And.intro (by
    intro index bounded
    change source16.get? (0 + index) = destination16_0.get? index
    have same : source16 = destination16_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length16 : (target16.map Setup.Block.length).sum = source16.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
