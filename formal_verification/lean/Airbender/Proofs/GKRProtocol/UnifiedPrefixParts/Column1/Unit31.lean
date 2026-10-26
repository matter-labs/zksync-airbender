import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source31 : Setup.Block := original.get ⟨31, by decide +kernel⟩

column_blocks_part part31_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 17 stop 18
noncomputable def destination31_0 : Setup.Block := part31_0.get ⟨0, by decide +kernel⟩

noncomputable def target31 : List Setup.Block := part31_0

theorem follows31 : blockTargetsFollow source31 0 target31 :=
  And.intro (by
    intro index bounded
    change source31.get? (0 + index) = destination31_0.get? index
    have same : source31 = destination31_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length31 : (target31.map Setup.Block.length).sum = source31.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
