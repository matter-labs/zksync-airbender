import GKRProtocol.UnifiedSpecialParts.Column6.Chunk189.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column6.Chunk189
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24280 : Setup.Block := original.get ⟨88, by decide +kernel⟩

column_blocks_part part24280_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24280 stop 24281
noncomputable def destination24280_0 : Setup.Block := part24280_0.get ⟨0, by decide +kernel⟩

noncomputable def target24280 : List Setup.Block := part24280_0

theorem follows24280 : blockTargetsFollow source24280 0 target24280 :=
  And.intro (by
    intro index bounded
    change source24280.get? (0 + index) = destination24280_0.get? index
    have same : source24280 = destination24280_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24280 : (target24280.map Setup.Block.length).sum = source24280.length := by decide +kernel

noncomputable def source24281 : Setup.Block := original.get ⟨89, by decide +kernel⟩

column_blocks_part part24281_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24281 stop 24282
noncomputable def destination24281_0 : Setup.Block := part24281_0.get ⟨0, by decide +kernel⟩

noncomputable def target24281 : List Setup.Block := part24281_0

theorem follows24281 : blockTargetsFollow source24281 0 target24281 :=
  And.intro (by
    intro index bounded
    change source24281.get? (0 + index) = destination24281_0.get? index
    have same : source24281 = destination24281_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24281 : (target24281.map Setup.Block.length).sum = source24281.length := by decide +kernel

noncomputable def source24282 : Setup.Block := original.get ⟨90, by decide +kernel⟩

column_blocks_part part24282_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24282 stop 24283
noncomputable def destination24282_0 : Setup.Block := part24282_0.get ⟨0, by decide +kernel⟩

noncomputable def target24282 : List Setup.Block := part24282_0

theorem follows24282 : blockTargetsFollow source24282 0 target24282 :=
  And.intro (by
    intro index bounded
    change source24282.get? (0 + index) = destination24282_0.get? index
    have same : source24282 = destination24282_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24282 : (target24282.map Setup.Block.length).sum = source24282.length := by decide +kernel

noncomputable def source24283 : Setup.Block := original.get ⟨91, by decide +kernel⟩

column_blocks_part part24283_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24283 stop 24284
noncomputable def destination24283_0 : Setup.Block := part24283_0.get ⟨0, by decide +kernel⟩

noncomputable def target24283 : List Setup.Block := part24283_0

theorem follows24283 : blockTargetsFollow source24283 0 target24283 :=
  And.intro (by
    intro index bounded
    change source24283.get? (0 + index) = destination24283_0.get? index
    have same : source24283 = destination24283_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24283 : (target24283.map Setup.Block.length).sum = source24283.length := by decide +kernel

noncomputable def source24284 : Setup.Block := original.get ⟨92, by decide +kernel⟩

column_blocks_part part24284_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24284 stop 24285
noncomputable def destination24284_0 : Setup.Block := part24284_0.get ⟨0, by decide +kernel⟩

noncomputable def target24284 : List Setup.Block := part24284_0

theorem follows24284 : blockTargetsFollow source24284 0 target24284 :=
  And.intro (by
    intro index bounded
    change source24284.get? (0 + index) = destination24284_0.get? index
    have same : source24284 = destination24284_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24284 : (target24284.map Setup.Block.length).sum = source24284.length := by decide +kernel

noncomputable def source24285 : Setup.Block := original.get ⟨93, by decide +kernel⟩

column_blocks_part part24285_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24285 stop 24286
noncomputable def destination24285_0 : Setup.Block := part24285_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24285_1 from (UnifiedReduced.Setup.nativeShiftData.columns[(6 : Nat)]) start 24286 stop 24287
noncomputable def destination24285_1 : Setup.Block := part24285_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24285_2 from (UnifiedReduced.Setup.nativeROMData.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24285_2 : Setup.Block := part24285_2.get ⟨0, by decide +kernel⟩

noncomputable def target24285 : List Setup.Block := part24285_0 ++ part24285_1 ++ part24285_2

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

noncomputable def source24286 : Setup.Block := original.get ⟨94, by decide +kernel⟩

column_blocks_part part24286_0 from (UnifiedReduced.Setup.nativeROMData.columns[(6 : Nat)]) start 1 stop 2
noncomputable def destination24286_0 : Setup.Block := part24286_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_1 : Setup.Block := part24286_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_2 : Setup.Block := part24286_2.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_3 from (UnifiedReduced.Setup.nativeRotate8Data.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_3 : Setup.Block := part24286_3.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_4 from (UnifiedReduced.Setup.nativeRotate7Data.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_4 : Setup.Block := part24286_4.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_5 from (UnifiedReduced.Setup.nativeConditionalData.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_5 : Setup.Block := part24286_5.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_6 from (UnifiedReduced.Setup.nativeXorData.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_6 : Setup.Block := part24286_6.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_7 from (UnifiedReduced.Setup.nativeOrData.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_7 : Setup.Block := part24286_7.get ⟨0, by decide +kernel⟩

column_blocks_part part24286_8 from (UnifiedReduced.Setup.nativeAndData.columns[(6 : Nat)]) start 0 stop 1
noncomputable def destination24286_8 : Setup.Block := part24286_8.get ⟨0, by decide +kernel⟩

noncomputable def part24286_9 : List Setup.Block := [.dense #[0, 0, 0, 0]]
noncomputable def destination24286_9 : Setup.Block := part24286_9.get ⟨0, by decide +kernel⟩

noncomputable def target24286 : List Setup.Block := part24286_0 ++ part24286_1 ++ part24286_2 ++ part24286_3 ++ part24286_4 ++ part24286_5 ++ part24286_6 ++ part24286_7 ++ part24286_8 ++ part24286_9

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
