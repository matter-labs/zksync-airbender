import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column5.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows24541 : blockTargetsFollow source24541 0 target24541 :=
  And.intro (by
    intro index bounded
    change source24541.get? (0 + index) = destination24541_0.get? index
    change (Setup.Block.periodic 9 0 #[255, 0, 0, 0, 0, 0, 0, 0]).get? (0 + index) =
      (Setup.Block.periodic 8 0 #[255, 0, 0, 0, 0, 0, 0, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 64 := bounded; omega : 0 + index < 72)
    · exact (show index < 64 from bounded)
    · exact (by decide +kernel : 0 % 8 = 0)
  ) (And.intro (by
    intro index bounded
    change source24541.get? (64 + index) = destination24541_1.get? index
    have checked : finiteBlockSpanRangeCheck source24541 destination24541_1 64 0 5 = true := by decide +kernel
    exact finite_block_span_range_sound source24541 destination24541_1 64 0 5 checked index (by omega) (by have : index < 5 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source24541.get? (69 + index) = destination24541_2.get? index
    have checked : finiteBlockSpanRangeCheck source24541 destination24541_2 69 0 3 = true := by decide +kernel
    exact finite_block_span_range_sound source24541 destination24541_2 69 0 3 checked index (by omega) (by have : index < 3 := bounded; omega)
  ) (True.intro)))

theorem length24541 : (target24541.map Setup.Block.length).sum = source24541.length := by decide +kernel

theorem follows24542 : blockTargetsFollow source24542 0 target24542 :=
  And.intro (by
    intro index bounded
    change source24542.get? (0 + index) = destination24542_0.get? index
    change (Setup.Block.affine 1114125 0 0).get? (0 + index) = (Setup.Block.affine 1048573 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048573 := bounded; omega : 0 + index < 1114125)
    · exact (show index < 1048573 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24542.get? (1048573 + index) = destination24542_1.get? index
    change (Setup.Block.affine 1114125 0 0).get? (1048573 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1048573 + index < 1114125)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24542.get? (1114109 + index) = destination24542_2.get? index
    change (Setup.Block.affine 1114125 0 0).get? (1114109 + index) = (Setup.Block.affine 16 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 16 := bounded; omega : 1114109 + index < 1114125)
    · exact (show index < 16 from bounded)
    · decide +kernel
  ) (True.intro)))

theorem length24542 : (target24542.map Setup.Block.length).sum = source24542.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
