import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column7.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows24668 : blockTargetsFollow source24668 0 target24668 :=
  And.intro (by
    intro index bounded
    change source24668.get? (0 + index) = destination24668_0.get? index
    change (Setup.Block.periodic 25 0 #[255, 0, 0, 0, 0, 0, 0, 0]).get? (0 + index) =
      (Setup.Block.periodic 24 0 #[255, 0, 0, 0, 0, 0, 0, 0]).get? index
    apply periodic_zero_block_span
    · exact (by have bound : index < 192 := bounded; omega : 0 + index < 200)
    · exact (show index < 192 from bounded)
    · exact (by decide +kernel : 0 % 8 = 0)
  ) (And.intro (by
    intro index bounded
    change source24668.get? (192 + index) = destination24668_1.get? index
    have checked : finiteBlockSpanRangeCheck source24668 destination24668_1 192 0 5 = true := by decide +kernel
    exact finite_block_span_range_sound source24668 destination24668_1 192 0 5 checked index (by omega) (by have : index < 5 := bounded; omega)
  ) (And.intro (by
    intro index bounded
    change source24668.get? (197 + index) = destination24668_2.get? index
    have checked : finiteBlockSpanRangeCheck source24668 destination24668_2 197 0 3 = true := by decide +kernel
    exact finite_block_span_range_sound source24668 destination24668_2 197 0 3 checked index (by omega) (by have : index < 3 := bounded; omega)
  ) (True.intro)))

theorem length24668 : (target24668.map Setup.Block.length).sum = source24668.length := by decide +kernel

theorem follows24669 : blockTargetsFollow source24669 0 target24669 :=
  And.intro (by
    intro index bounded
    change source24669.get? (0 + index) = destination24669_0.get? index
    change (Setup.Block.affine 1507457 0 0).get? (0 + index) = (Setup.Block.affine 1048573 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048573 := bounded; omega : 0 + index < 1507457)
    · exact (show index < 1048573 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1048573 + index) = destination24669_1.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1048573 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1048573 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1114109 + index) = destination24669_2.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1114109 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1114109 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1179645 + index) = destination24669_3.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1179645 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1179645 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1245181 + index) = destination24669_4.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1245181 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1245181 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1310717 + index) = destination24669_5.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1310717 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 1310717 + index < 1507457)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1310845 + index) = destination24669_6.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1310845 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1310845 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1376381 + index) = destination24669_7.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1376381 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1376381 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1441917 + index) = destination24669_8.get? index
    change (Setup.Block.affine 1507457 0 0).get? (1441917 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 1441917 + index < 1507457)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24669.get? (1507453 + index) = destination24669_9.get? index
    have checked : finiteBlockSpanRangeCheck source24669 destination24669_9 1507453 0 4 = true := by decide +kernel
    exact finite_block_span_range_sound source24669 destination24669_9 1507453 0 4 checked index (by omega) (by have : index < 4 := bounded; omega)
  ) (True.intro))))))))))

theorem length24669 : (target24669.map Setup.Block.length).sum = source24669.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
