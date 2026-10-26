import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk206.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk206
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source26488 : Setup.Block := original.get ⟨120, by decide +kernel⟩

column_blocks_part part26488_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1030 stop 1031
noncomputable def destination26488_0 : Setup.Block := part26488_0.get ⟨0, by decide +kernel⟩

noncomputable def target26488 : List Setup.Block := part26488_0

theorem follows26488 : blockTargetsFollow source26488 0 target26488 :=
  And.intro (by
    intro index bounded
    change source26488.get? (0 + index) = destination26488_0.get? index
    have same : source26488 = destination26488_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26488 : (target26488.map Setup.Block.length).sum = source26488.length := by decide +kernel

noncomputable def source26489 : Setup.Block := original.get ⟨121, by decide +kernel⟩

column_blocks_part part26489_0 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(5 : Nat)]) start 1031 stop 1032
noncomputable def destination26489_0 : Setup.Block := part26489_0.get ⟨0, by decide +kernel⟩

noncomputable def target26489 : List Setup.Block := part26489_0

theorem follows26489 : blockTargetsFollow source26489 0 target26489 :=
  And.intro (by
    intro index bounded
    change source26489.get? (0 + index) = destination26489_0.get? index
    have same : source26489 = destination26489_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length26489 : (target26489.map Setup.Block.length).sum = source26489.length := by decide +kernel

noncomputable def source26490 : Setup.Block := original.get ⟨122, by decide +kernel⟩

column_blocks_part part26490_0 from (UnifiedReduced.Setup.nativeConditionalData.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination26490_0 : Setup.Block := part26490_0.get ⟨0, by decide +kernel⟩

column_blocks_part part26490_1 from (UnifiedReduced.Setup.nativeXorData.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination26490_1 : Setup.Block := part26490_1.get ⟨0, by decide +kernel⟩

column_blocks_part part26490_2 from (UnifiedReduced.Setup.nativeOrData.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination26490_2 : Setup.Block := part26490_2.get ⟨0, by decide +kernel⟩

column_blocks_part part26490_3 from (UnifiedReduced.Setup.nativeAndData.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination26490_3 : Setup.Block := part26490_3.get ⟨0, by decide +kernel⟩

noncomputable def part26490_4 : List Setup.Block := [.dense #[0]]
noncomputable def destination26490_4 : Setup.Block := part26490_4.get ⟨0, by decide +kernel⟩

noncomputable def target26490 : List Setup.Block := part26490_0 ++ part26490_1 ++ part26490_2 ++ part26490_3 ++ part26490_4

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
