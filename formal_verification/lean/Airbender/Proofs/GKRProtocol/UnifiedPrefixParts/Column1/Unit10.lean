import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source10 : Setup.Block := original.get ⟨10, by decide +kernel⟩

column_blocks_part part10_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(1 : Nat)]) start 2 stop 3
noncomputable def destination10_0 : Setup.Block := part10_0.get ⟨0, by decide +kernel⟩

noncomputable def target10 : List Setup.Block := part10_0

theorem follows10 : blockTargetsFollow source10 0 target10 :=
  And.intro (by
    intro index bounded
    change source10.get? (0 + index) = destination10_0.get? index
    have same : source10 = destination10_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length10 : (target10.map Setup.Block.length).sum = source10.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
