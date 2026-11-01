import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column4.Projected
import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column4.Chunk199.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem follows25569 : blockTargetsFollow source25569 0 target25569 :=
  And.intro (by
    intro index bounded
    change source25569.get? (0 + index) = destination25569_0.get? index
    change (Setup.Block.affine 327809 0 0).get? (0 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 0 + index < 327809)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source25569.get? (65536 + index) = destination25569_1.get? index
    change (Setup.Block.affine 327809 0 0).get? (65536 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 65536 + index < 327809)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source25569.get? (131072 + index) = destination25569_2.get? index
    change (Setup.Block.affine 327809 0 0).get? (131072 + index) = (Setup.Block.affine 128 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 128 := bounded; omega : 131072 + index < 327809)
    · exact (show index < 128 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source25569.get? (131200 + index) = destination25569_3.get? index
    change (Setup.Block.affine 327809 0 0).get? (131200 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 131200 + index < 327809)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source25569.get? (196736 + index) = destination25569_4.get? index
    change (Setup.Block.affine 327809 0 0).get? (196736 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 196736 + index < 327809)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source25569.get? (262272 + index) = destination25569_5.get? index
    change (Setup.Block.affine 327809 0 0).get? (262272 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 262272 + index < 327809)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source25569.get? (327808 + index) = destination25569_6.get? index
    have checked : finiteBlockSpanRangeCheck source25569 destination25569_6 327808 0 1 = true := by decide +kernel
    exact finite_block_span_range_sound source25569 destination25569_6 327808 0 1 checked index (by omega) (by have : index < 1 := bounded; omega)
  ) (True.intro)))))))

theorem length25569 : (target25569.map Setup.Block.length).sum = source25569.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk199
