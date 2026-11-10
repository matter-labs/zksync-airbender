import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column2.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows12 : blockTargetsFollow source12 0 target12 :=
  And.intro (by
    intro index bounded
    change source12.get? (0 + index) = destination12_0.get? index
    have same : source12 = destination12_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length12 : (target12.map Setup.Block.length).sum = source12.length := by decide +kernel

theorem follows13 : blockTargetsFollow source13 0 target13 :=
  And.intro (by
    intro index bounded
    change source13.get? (0 + index) = destination13_0.get? index
    change (Setup.Block.affine 1245308 0 0).get? (0 + index) = (Setup.Block.affine 1048572 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048572 := bounded; omega : 0 + index < 1245308)
    · exact (show index < 1048572 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source13.get? (1048572 + index) = destination13_1.get? index
    change (Setup.Block.affine 1245308 0 0).get? (1048572 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1048572 + index < 1245308)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source13.get? (1114108 + index) = destination13_2.get? index
    change (Setup.Block.affine 1245308 0 0).get? (1114108 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1114108 + index < 1245308)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source13.get? (1179644 + index) = destination13_3.get? index
    change (Setup.Block.affine 1245308 0 0).get? (1179644 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1179644 + index < 1245308)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source13.get? (1245180 + index) = destination13_4.get? index
    change (Setup.Block.affine 1245308 0 0).get? (1245180 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 1245180 + index < 1245308)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (True.intro)))))

theorem length13 : (target13.map Setup.Block.length).sum = source13.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
