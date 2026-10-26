import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source17 : Setup.Block := original.get ⟨17, by decide +kernel⟩

column_blocks_part part17_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 3 stop 4
noncomputable def destination17_0 : Setup.Block := part17_0.get ⟨0, by decide +kernel⟩

noncomputable def target17 : List Setup.Block := part17_0

theorem follows17 : blockTargetsFollow source17 0 target17 :=
  And.intro (by
    intro index bounded
    change source17.get? (0 + index) = destination17_0.get? index
    have same : source17 = destination17_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length17 : (target17.map Setup.Block.length).sum = source17.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
