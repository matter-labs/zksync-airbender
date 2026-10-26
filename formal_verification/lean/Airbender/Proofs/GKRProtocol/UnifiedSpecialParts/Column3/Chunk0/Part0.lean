import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column3.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source0 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part0_0 from (UnifiedReduced.Setup.nativeZeroData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_0 : Setup.Block := part0_0.get ⟨0, by decide +kernel⟩

column_blocks_part part0_1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_1 : Setup.Block := part0_1.get ⟨0, by decide +kernel⟩

column_blocks_part part0_2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_2 : Setup.Block := part0_2.get ⟨0, by decide +kernel⟩

column_blocks_part part0_3 from (UnifiedReduced.Setup.nativeByteSignData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_3 : Setup.Block := part0_3.get ⟨0, by decide +kernel⟩

column_blocks_part part0_4 from (UnifiedReduced.Setup.nativeSignData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_4 : Setup.Block := part0_4.get ⟨0, by decide +kernel⟩

column_blocks_part part0_5 from (UnifiedReduced.Setup.nativeTruncationData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_5 : Setup.Block := part0_5.get ⟨0, by decide +kernel⟩

column_blocks_part part0_6 from (UnifiedReduced.Setup.nativeShiftData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination0_6 : Setup.Block := part0_6.get ⟨0, by decide +kernel⟩

noncomputable def target0 : List Setup.Block := part0_0 ++ part0_1 ++ part0_2 ++ part0_3 ++ part0_4 ++ part0_5 ++ part0_6

theorem follows0 : blockTargetsFollow source0 0 target0 :=
  And.intro (by
    intro index bounded
    change source0.get? (0 + index) = destination0_0.get? index
    change (Setup.Block.affine 327938 0 0).get? (0 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 0 + index < 327938)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1 + index) = destination0_1.get? index
    change (Setup.Block.affine 327938 0 0).get? (1 + index) = (Setup.Block.affine 131072 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 131072 := bounded; omega : 1 + index < 327938)
    · exact (show index < 131072 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (131073 + index) = destination0_2.get? index
    change (Setup.Block.affine 327938 0 0).get? (131073 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 131073 + index < 327938)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (196609 + index) = destination0_3.get? index
    change (Setup.Block.affine 327938 0 0).get? (196609 + index) = (Setup.Block.affine 256 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 256 := bounded; omega : 196609 + index < 327938)
    · exact (show index < 256 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (196865 + index) = destination0_4.get? index
    change (Setup.Block.affine 327938 0 0).get? (196865 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 196865 + index < 327938)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (262401 + index) = destination0_5.get? index
    change (Setup.Block.affine 327938 0 0).get? (262401 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 262401 + index < 327938)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (327937 + index) = destination0_6.get? index
    change (Setup.Block.affine 327938 0 0).get? (327937 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 327937 + index < 327938)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (True.intro)))))))

theorem length0 : (target0.map Setup.Block.length).sum = source0.length := by decide +kernel

noncomputable def source1 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part1_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(3 : Nat)]) start 1 stop 2
noncomputable def destination1_0 : Setup.Block := part1_0.get ⟨0, by decide +kernel⟩

column_blocks_part part1_1 from (UnifiedReduced.Setup.nativeShiftData.columns[(3 : Nat)]) start 2 stop 3
noncomputable def destination1_1 : Setup.Block := part1_1.get ⟨0, by decide +kernel⟩

column_blocks_part part1_2 from (UnifiedReduced.Setup.nativeROMData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination1_2 : Setup.Block := part1_2.get ⟨0, by decide +kernel⟩

noncomputable def target1 : List Setup.Block := part1_0 ++ part1_1 ++ part1_2

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

noncomputable def source2 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part2_0 from (UnifiedReduced.Setup.nativeROMData.columns[(3 : Nat)]) start 1 stop 2
noncomputable def destination2_0 : Setup.Block := part2_0.get ⟨0, by decide +kernel⟩

column_blocks_part part2_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_1 : Setup.Block := part2_1.get ⟨0, by decide +kernel⟩

column_blocks_part part2_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_2 : Setup.Block := part2_2.get ⟨0, by decide +kernel⟩

column_blocks_part part2_3 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_3 : Setup.Block := part2_3.get ⟨0, by decide +kernel⟩

column_blocks_part part2_4 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_4 : Setup.Block := part2_4.get ⟨0, by decide +kernel⟩

column_blocks_part part2_5 from (UnifiedReduced.Setup.nativeConditionalData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_5 : Setup.Block := part2_5.get ⟨0, by decide +kernel⟩

column_blocks_part part2_6 from (UnifiedReduced.Setup.nativeXorData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_6 : Setup.Block := part2_6.get ⟨0, by decide +kernel⟩

column_blocks_part part2_7 from (UnifiedReduced.Setup.nativeOrData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_7 : Setup.Block := part2_7.get ⟨0, by decide +kernel⟩

column_blocks_part part2_8 from (UnifiedReduced.Setup.nativeAndData.columns[(3 : Nat)]) start 0 stop 1
noncomputable def destination2_8 : Setup.Block := part2_8.get ⟨0, by decide +kernel⟩

noncomputable def part2_9 : List Setup.Block := [.dense #[0, 0, 0]]
noncomputable def destination2_9 : Setup.Block := part2_9.get ⟨0, by decide +kernel⟩

noncomputable def target2 : List Setup.Block := part2_0 ++ part2_1 ++ part2_2 ++ part2_3 ++ part2_4 ++ part2_5 ++ part2_6 ++ part2_7 ++ part2_8 ++ part2_9

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
