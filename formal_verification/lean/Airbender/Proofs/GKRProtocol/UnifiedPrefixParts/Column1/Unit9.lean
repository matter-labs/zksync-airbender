import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source9 : Setup.Block := original.get ⟨9, by decide +kernel⟩

column_blocks_part part9_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination9_0 : Setup.Block := part9_0.get ⟨0, by decide +kernel⟩

noncomputable def target9 : List Setup.Block := part9_0

theorem follows9 : blockTargetsFollow source9 0 target9 :=
  And.intro (by
    intro index bounded
    change source9.get? (0 + index) = destination9_0.get? index
    have same : source9 = destination9_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length9 : (target9.map Setup.Block.length).sum = source9.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
