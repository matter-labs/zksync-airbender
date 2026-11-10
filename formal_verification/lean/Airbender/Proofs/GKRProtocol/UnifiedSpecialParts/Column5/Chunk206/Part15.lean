import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column5.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk206.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows26490 : blockTargetsFollow source26490 0 target26490 :=
  And.intro (by
    intro index bounded
    change source26490.get? (0 + index) = destination26490_0.get? index
    change (Setup.Block.affine 196737 0 0).get? (0 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 0 + index < 196737)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source26490.get? (128 + index) = destination26490_1.get? index
    change (Setup.Block.affine 196737 0 0).get? (128 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 128 + index < 196737)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source26490.get? (65664 + index) = destination26490_2.get? index
    change (Setup.Block.affine 196737 0 0).get? (65664 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 65664 + index < 196737)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source26490.get? (131200 + index) = destination26490_3.get? index
    change (Setup.Block.affine 196737 0 0).get? (131200 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 131200 + index < 196737)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source26490.get? (196736 + index) = destination26490_4.get? index
    have checked : finiteBlockSpanRangeCheck source26490 destination26490_4 196736 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source26490 destination26490_4 196736 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (True.intro)))))

theorem length26490 : (target26490.map Setup.Block.length).sum = source26490.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
