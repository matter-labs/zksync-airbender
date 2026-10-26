import Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source32 : Setup.Block := original.get ⟨32, by decide +kernel⟩

column_blocks_part part32_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(1 : Nat)]) start 18 stop 19
noncomputable def destination32_0 : Setup.Block := part32_0.get ⟨0, by decide +kernel⟩

column_blocks_part part32_1 from (UnifiedReduced.Setup.nativeXorData.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination32_1 : Setup.Block := part32_1.get ⟨0, by decide +kernel⟩

noncomputable def target32 : List Setup.Block := part32_0 ++ part32_1

theorem follows32 : blockTargetsFollow source32 0 target32 :=
  And.intro (by
    intro index bounded
    change source32.get? (0 + index) = destination32_0.get? index
    change (Setup.Block.affine 5 0 0).get? (0 + index) = (Setup.Block.affine 4 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 4 := bounded; omega : 0 + index < 5)
    · exact (show index < 4 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source32.get? (4 + index) = destination32_1.get? index
    change (Setup.Block.affine 5 0 0).get? (4 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 4 + index < 5)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (True.intro))

theorem length32 : (target32.map Setup.Block.length).sum = source32.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
