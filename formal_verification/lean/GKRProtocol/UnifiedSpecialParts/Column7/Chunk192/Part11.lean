import GKRProtocol.UnifiedSpecialParts.Column7.Chunk192.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column7.Chunk192
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24664 : Setup.Block := original.get ⟨88, by decide +kernel⟩

column_blocks_part part24664_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24664 stop 24665
noncomputable def destination24664_0 : Setup.Block := part24664_0.get ⟨0, by decide +kernel⟩

noncomputable def target24664 : List Setup.Block := part24664_0

theorem follows24664 : blockTargetsFollow source24664 0 target24664 :=
  And.intro (by
    intro index bounded
    change source24664.get? (0 + index) = destination24664_0.get? index
    have same : source24664 = destination24664_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24664 : (target24664.map Setup.Block.length).sum = source24664.length := by decide +kernel

noncomputable def source24665 : Setup.Block := original.get ⟨89, by decide +kernel⟩

column_blocks_part part24665_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24665 stop 24666
noncomputable def destination24665_0 : Setup.Block := part24665_0.get ⟨0, by decide +kernel⟩

noncomputable def target24665 : List Setup.Block := part24665_0

theorem follows24665 : blockTargetsFollow source24665 0 target24665 :=
  And.intro (by
    intro index bounded
    change source24665.get? (0 + index) = destination24665_0.get? index
    have same : source24665 = destination24665_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24665 : (target24665.map Setup.Block.length).sum = source24665.length := by decide +kernel

noncomputable def source24666 : Setup.Block := original.get ⟨90, by decide +kernel⟩

column_blocks_part part24666_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24666 stop 24667
noncomputable def destination24666_0 : Setup.Block := part24666_0.get ⟨0, by decide +kernel⟩

noncomputable def target24666 : List Setup.Block := part24666_0

theorem follows24666 : blockTargetsFollow source24666 0 target24666 :=
  And.intro (by
    intro index bounded
    change source24666.get? (0 + index) = destination24666_0.get? index
    have same : source24666 = destination24666_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24666 : (target24666.map Setup.Block.length).sum = source24666.length := by decide +kernel

noncomputable def source24667 : Setup.Block := original.get ⟨91, by decide +kernel⟩

column_blocks_part part24667_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24667 stop 24668
noncomputable def destination24667_0 : Setup.Block := part24667_0.get ⟨0, by decide +kernel⟩

noncomputable def target24667 : List Setup.Block := part24667_0

theorem follows24667 : blockTargetsFollow source24667 0 target24667 :=
  And.intro (by
    intro index bounded
    change source24667.get? (0 + index) = destination24667_0.get? index
    have same : source24667 = destination24667_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24667 : (target24667.map Setup.Block.length).sum = source24667.length := by decide +kernel

noncomputable def source24668 : Setup.Block := original.get ⟨92, by decide +kernel⟩

column_blocks_part part24668_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24668 stop 24669
noncomputable def destination24668_0 : Setup.Block := part24668_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24668_1 from (UnifiedReduced.Setup.nativeShiftData.columns[(7 : Nat)]) start 24669 stop 24670
noncomputable def destination24668_1 : Setup.Block := part24668_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24668_2 from (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24668_2 : Setup.Block := part24668_2.get ⟨0, by decide +kernel⟩

noncomputable def target24668 : List Setup.Block := part24668_0 ++ part24668_1 ++ part24668_2

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

noncomputable def source24669 : Setup.Block := original.get ⟨93, by decide +kernel⟩

column_blocks_part part24669_0 from (UnifiedReduced.Setup.nativeROMData.columns[(7 : Nat)]) start 1 stop 2
noncomputable def destination24669_0 : Setup.Block := part24669_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_1 : Setup.Block := part24669_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_2 : Setup.Block := part24669_2.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_3 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_3 : Setup.Block := part24669_3.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_4 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_4 : Setup.Block := part24669_4.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_5 from (UnifiedReduced.Setup.nativeConditionalData.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_5 : Setup.Block := part24669_5.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_6 from (UnifiedReduced.Setup.nativeXorData.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_6 : Setup.Block := part24669_6.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_7 from (UnifiedReduced.Setup.nativeOrData.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_7 : Setup.Block := part24669_7.get ⟨0, by decide +kernel⟩

column_blocks_part part24669_8 from (UnifiedReduced.Setup.nativeAndData.columns[(7 : Nat)]) start 0 stop 1
noncomputable def destination24669_8 : Setup.Block := part24669_8.get ⟨0, by decide +kernel⟩

noncomputable def part24669_9 : List Setup.Block := [.dense #[0, 0, 0, 0]]
noncomputable def destination24669_9 : Setup.Block := part24669_9.get ⟨0, by decide +kernel⟩

noncomputable def target24669 : List Setup.Block := part24669_0 ++ part24669_1 ++ part24669_2 ++ part24669_3 ++ part24669_4 ++ part24669_5 ++ part24669_6 ++ part24669_7 ++ part24669_8 ++ part24669_9

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
