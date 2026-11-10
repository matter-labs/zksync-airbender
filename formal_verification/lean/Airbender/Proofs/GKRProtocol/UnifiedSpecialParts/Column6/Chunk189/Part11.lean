import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column6.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows24285 : blockTargetsFollow source24285 0 target24285 :=
  And.intro (by
    intro index bounded
    change source24285.get? (0 + index) = destination24285_0.get? index
    change (Setup.Block.periodic 17 0 #[255, 0, 0, 0, 0, 0, 0, 0]).get? (0 + index) =
      (Setup.Block.periodic 16 0 #[255, 0, 0, 0, 0, 0, 0, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 128 := bounded; omega : 0 + index < 136)
    · exact (show index < 128 from bounded)
    · exact (by decide +kernel : 0 % 8 = 0)
  ) (And.intro (by
    intro index bounded
    change source24285.get? (128 + index) = destination24285_1.get? index
    have checked : finiteBlockSpanRangeCheck source24285 destination24285_1 128 0 5 = true := by decide +kernel
    exact finite_block_span_range_sound source24285 destination24285_1 128 0 5 checked index (by omega) (by have : index < 5 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source24285.get? (133 + index) = destination24285_2.get? index
    have checked : finiteBlockSpanRangeCheck source24285 destination24285_2 133 0 3 = true := by decide +kernel
    exact finite_block_span_range_sound source24285 destination24285_2 133 0 3 checked index (by omega) (by have : index < 3 := bounded; omega)
  ) (True.intro)))

theorem length24285 : (target24285.map Setup.Block.length).sum = source24285.length := by decide +kernel

theorem follows24286 : blockTargetsFollow source24286 0 target24286 :=
  And.intro (by
    intro index bounded
    change source24286.get? (0 + index) = destination24286_0.get? index
    change (Setup.Block.affine 1507457 0 0).get? (0 + index) = (Setup.Block.affine 1048573 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048573 := bounded; omega : 0 + index < 1507457)
    · exact (show index < 1048573 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1048573 + index) = destination24286_1.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1048573 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1048573 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1114109 + index) = destination24286_2.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1114109 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1114109 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1179645 + index) = destination24286_3.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1179645 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1179645 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1245181 + index) = destination24286_4.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1245181 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1245181 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1310717 + index) = destination24286_5.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1310717 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 1310717 + index < 1507457)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1310845 + index) = destination24286_6.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1310845 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1310845 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1376381 + index) = destination24286_7.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1376381 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1376381 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1441917 + index) = destination24286_8.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1441917 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1441917 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24286.get? (1507453 + index) = destination24286_9.get? index
    have checked : finiteBlockSpanRangeCheck source24286 destination24286_9 1507453 0 4 = true := by decide +kernel
    exact finite_block_span_range_sound source24286 destination24286_9 1507453 0 4 checked index (by omega) (by have : index < 4 := bounded; omega)
  ) (True.intro))))))))))

theorem length24286 : (target24286.map Setup.Block.length).sum = source24286.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
