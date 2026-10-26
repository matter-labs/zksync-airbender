import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source21 : Setup.Block := original.get ⟨21, by decide +kernel⟩

column_blocks_part part21_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 7 stop 8
noncomputable def destination21_0 : Setup.Block := part21_0.get ⟨0, by decide +kernel⟩

noncomputable def target21 : List Setup.Block := part21_0

theorem follows21 : blockTargetsFollow source21 0 target21 :=
  And.intro (by
    intro index bounded
    change source21.get? (0 + index) = destination21_0.get? index
    have same : source21 = destination21_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length21 : (target21.map Setup.Block.length).sum = source21.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
