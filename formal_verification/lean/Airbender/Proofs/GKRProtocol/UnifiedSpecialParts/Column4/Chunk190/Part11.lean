import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column4.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows24414 : blockTargetsFollow source24414 0 target24414 :=
  And.intro (by
    intro index bounded
    change source24414.get? (0 + index) = destination24414_0.get? index
    change (Setup.Block.affine 1048581 0 0).get? (0 + index) = (Setup.Block.affine 4 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 4 := bounded; omega : 0 + index < 1048581)
    · exact (show index < 4 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24414.get? (4 + index) = destination24414_1.get? index
    change (Setup.Block.affine 1048581 0 0).get? (4 + index) = (Setup.Block.affine 1048576 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048576 := bounded; omega : 4 + index < 1048581)
    · exact (show index < 1048576 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24414.get? (1048580 + index) = destination24414_2.get? index
    change (Setup.Block.affine 1048581 0 0).get? (1048580 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 1048580 + index < 1048581)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (True.intro)))

theorem length24414 : (target24414.map Setup.Block.length).sum = source24414.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
