import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column3.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows1 : blockTargetsFollow source1 0 target1 :=
  And.intro (by
    intro index bounded
    change source1.get? (0 + index) = destination1_0.get? index
    change (Setup.Block.periodic 32768 0 #[1, 2, 3, 4, 5, 6, 7, 0]).get? (0 + index) =
      (Setup.Block.periodic 32767 0 #[1, 2, 3, 4, 5, 6, 7, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 262136 := bounded; omega : 0 + index < 262144)
    · exact (show index < 262136 from bounded)
    · exact (by decide +kernel : 0 % 8 = 0)
  ) (And.intro (by
    intro index bounded
    change source1.get? (262136 + index) = destination1_1.get? index
    have checked : finiteBlockSpanRangeCheck source1 destination1_1 262136 0 7 = true := by decide +kernel
    exact finite_block_span_range_sound source1 destination1_1 262136 0 7 checked index (by omega) (by have : index < 7 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source1.get? (262143 + index) = destination1_2.get? index
    have checked : finiteBlockSpanRangeCheck source1 destination1_2 262143 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source1 destination1_2 262143 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (True.intro)))

theorem length1 : (target1.map Setup.Block.length).sum = source1.length := by decide +kernel

theorem follows2 : blockTargetsFollow source2 0 target2 :=
  And.intro (by
    intro index bounded
    change source2.get? (0 + index) = destination2_0.get? index
    change (Setup.Block.affine 1507458 0 0).get? (0 + index) = (Setup.Block.affine 1048575 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048575 := bounded; omega : 0 + index < 1507458)
    · exact (show index < 1048575 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1048575 + index) = destination2_1.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1048575 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1048575 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1114111 + index) = destination2_2.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1114111 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1114111 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1179647 + index) = destination2_3.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1179647 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1179647 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1245183 + index) = destination2_4.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1245183 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1245183 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1310719 + index) = destination2_5.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1310719 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 1310719 + index < 1507458)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1310847 + index) = destination2_6.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1310847 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1310847 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1376383 + index) = destination2_7.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1376383 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1376383 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1441919 + index) = destination2_8.get? index
    change (Setup.Block.affine 1507458 0 0).get? (1441919 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1441919 + index < 1507458)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (1507455 + index) = destination2_9.get? index
    have checked : finiteBlockSpanRangeCheck source2 destination2_9 1507455 0 3 = true := by decide +kernel
    exact finite_block_span_range_sound source2 destination2_9 1507455 0 3 checked index (by omega) (by have : index < 3 := bounded; omega)
  ) (True.intro))))))))))

theorem length2 : (target2.map Setup.Block.length).sum = source2.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
