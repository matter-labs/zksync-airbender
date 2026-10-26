import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source29 : Setup.Block := original.get ⟨29, by decide +kernel⟩

column_blocks_part part29_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 15 stop 16
noncomputable def destination29_0 : Setup.Block := part29_0.get ⟨0, by decide +kernel⟩

noncomputable def target29 : List Setup.Block := part29_0

theorem follows29 : blockTargetsFollow source29 0 target29 :=
  And.intro (by
    intro index bounded
    change source29.get? (0 + index) = destination29_0.get? index
    have same : source29 = destination29_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length29 : (target29.map Setup.Block.length).sum = source29.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
