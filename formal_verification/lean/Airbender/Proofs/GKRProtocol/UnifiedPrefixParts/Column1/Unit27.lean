import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source27 : Setup.Block := original.get ⟨27, by decide +kernel⟩

column_blocks_part part27_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 13 stop 14
noncomputable def destination27_0 : Setup.Block := part27_0.get ⟨0, by decide +kernel⟩

noncomputable def target27 : List Setup.Block := part27_0

theorem follows27 : blockTargetsFollow source27 0 target27 :=
  And.intro (by
    intro index bounded
    change source27.get? (0 + index) = destination27_0.get? index
    have same : source27 = destination27_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length27 : (target27.map Setup.Block.length).sum = source27.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
