import GKRProtocol.UnifiedPrefixParts.Column1.Foundation

namespace Airbender.Compiler.UnifiedPrefixNative.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source13 : Setup.Block := original.get ⟨13, by decide +kernel⟩

column_blocks_part part13_0 from (UnifiedReduced.Setup.nativeROMData.columns[(1 : Nat)]) start 1 stop 2
noncomputable def destination13_0 : Setup.Block := part13_0.get ⟨0, by decide +kernel⟩

column_blocks_part part13_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(1 : Nat)]) start 0 stop 1
noncomputable def destination13_1 : Setup.Block := part13_1.get ⟨0, by decide +kernel⟩

noncomputable def target13 : List Setup.Block := part13_0 ++ part13_1

theorem follows13 : blockTargetsFollow source13 0 target13 :=
  And.intro (by
    intro index bounded
    change source13.get? (0 + index) = destination13_0.get? index
    change (Setup.Block.affine 1048573 0 0).get? (0 + index) = (Setup.Block.affine 1048572 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048572 := bounded; omega : 0 + index < 1048573)
    · exact (show index < 1048572 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source13.get? (1048572 + index) = destination13_1.get? index
    change (Setup.Block.affine 1048573 0 0).get? (1048572 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 1048572 + index < 1048573)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (True.intro))

theorem length13 : (target13.map Setup.Block.length).sum = source13.length := by decide +kernel

end Airbender.Compiler.UnifiedPrefixNative.Column1
