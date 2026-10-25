import GKRProtocol.UnifiedSpecialParts.Column4.Chunk190.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24408 : Setup.Block := original.get ⟨88, by decide +kernel⟩

column_blocks_part part24408_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24408 stop 24409
noncomputable def destination24408_0 : Setup.Block := part24408_0.get ⟨0, by decide +kernel⟩

noncomputable def target24408 : List Setup.Block := part24408_0

theorem follows24408 : blockTargetsFollow source24408 0 target24408 :=
  And.intro (by
    intro index bounded
    change source24408.get? (0 + index) = destination24408_0.get? index
    have same : source24408 = destination24408_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24408 : (target24408.map Setup.Block.length).sum = source24408.length := by decide +kernel

noncomputable def source24409 : Setup.Block := original.get ⟨89, by decide +kernel⟩

column_blocks_part part24409_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24409 stop 24410
noncomputable def destination24409_0 : Setup.Block := part24409_0.get ⟨0, by decide +kernel⟩

noncomputable def target24409 : List Setup.Block := part24409_0

theorem follows24409 : blockTargetsFollow source24409 0 target24409 :=
  And.intro (by
    intro index bounded
    change source24409.get? (0 + index) = destination24409_0.get? index
    have same : source24409 = destination24409_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24409 : (target24409.map Setup.Block.length).sum = source24409.length := by decide +kernel

noncomputable def source24410 : Setup.Block := original.get ⟨90, by decide +kernel⟩

column_blocks_part part24410_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24410 stop 24411
noncomputable def destination24410_0 : Setup.Block := part24410_0.get ⟨0, by decide +kernel⟩

noncomputable def target24410 : List Setup.Block := part24410_0

theorem follows24410 : blockTargetsFollow source24410 0 target24410 :=
  And.intro (by
    intro index bounded
    change source24410.get? (0 + index) = destination24410_0.get? index
    have same : source24410 = destination24410_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24410 : (target24410.map Setup.Block.length).sum = source24410.length := by decide +kernel

noncomputable def source24411 : Setup.Block := original.get ⟨91, by decide +kernel⟩

column_blocks_part part24411_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24411 stop 24412
noncomputable def destination24411_0 : Setup.Block := part24411_0.get ⟨0, by decide +kernel⟩

noncomputable def target24411 : List Setup.Block := part24411_0

theorem follows24411 : blockTargetsFollow source24411 0 target24411 :=
  And.intro (by
    intro index bounded
    change source24411.get? (0 + index) = destination24411_0.get? index
    have same : source24411 = destination24411_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24411 : (target24411.map Setup.Block.length).sum = source24411.length := by decide +kernel

noncomputable def source24412 : Setup.Block := original.get ⟨92, by decide +kernel⟩

column_blocks_part part24412_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24412 stop 24413
noncomputable def destination24412_0 : Setup.Block := part24412_0.get ⟨0, by decide +kernel⟩

noncomputable def target24412 : List Setup.Block := part24412_0

theorem follows24412 : blockTargetsFollow source24412 0 target24412 :=
  And.intro (by
    intro index bounded
    change source24412.get? (0 + index) = destination24412_0.get? index
    have same : source24412 = destination24412_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24412 : (target24412.map Setup.Block.length).sum = source24412.length := by decide +kernel

noncomputable def source24413 : Setup.Block := original.get ⟨93, by decide +kernel⟩

column_blocks_part part24413_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24413 stop 24414
noncomputable def destination24413_0 : Setup.Block := part24413_0.get ⟨0, by decide +kernel⟩

noncomputable def target24413 : List Setup.Block := part24413_0

theorem follows24413 : blockTargetsFollow source24413 0 target24413 :=
  And.intro (by
    intro index bounded
    change source24413.get? (0 + index) = destination24413_0.get? index
    have same : source24413 = destination24413_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24413 : (target24413.map Setup.Block.length).sum = source24413.length := by decide +kernel

noncomputable def source24414 : Setup.Block := original.get ⟨94, by decide +kernel⟩

column_blocks_part part24414_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(4 : Nat)]) start 24414 stop 24415
noncomputable def destination24414_0 : Setup.Block := part24414_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24414_1 from (UnifiedReduced.Setup.nativeROMData.columns[(4 : Nat)]) start 0 stop 1
noncomputable def destination24414_1 : Setup.Block := part24414_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24414_2 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 0 stop 1
noncomputable def destination24414_2 : Setup.Block := part24414_2.get ⟨0, by decide +kernel⟩

noncomputable def target24414 : List Setup.Block := part24414_0 ++ part24414_1 ++ part24414_2

theorem follows24414 : blockTargetsFollow source24414 0 target24414 :=
  And.intro (by
    intro index bounded
    change source24414.get? (0 + index) = destination24414_0.get? index
    change (Setup.Block.affine 1048581 0 0).get? (0 + index) = (Setup.Block.affine 4 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 4 := bounded; omega : 0 + index < 1048581)
    · exact (show index < 4 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24414.get? (4 + index) = destination24414_1.get? index
    change (Setup.Block.affine 1048581 0 0).get? (4 + index) = (Setup.Block.affine 1048576 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1048576 := bounded; omega : 4 + index < 1048581)
    · exact (show index < 1048576 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source24414.get? (1048580 + index) = destination24414_2.get? index
    change (Setup.Block.affine 1048581 0 0).get? (1048580 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 1048580 + index < 1048581)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (True.intro)))

theorem length24414 : (target24414.map Setup.Block.length).sum = source24414.length := by decide +kernel

noncomputable def source24415 : Setup.Block := original.get ⟨95, by decide +kernel⟩

column_blocks_part part24415_0 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(4 : Nat)]) start 1 stop 2
noncomputable def destination24415_0 : Setup.Block := part24415_0.get ⟨0, by decide +kernel⟩

noncomputable def target24415 : List Setup.Block := part24415_0

theorem follows24415 : blockTargetsFollow source24415 0 target24415 :=
  And.intro (by
    intro index bounded
    change source24415.get? (0 + index) = destination24415_0.get? index
    have same : source24415 = destination24415_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24415 : (target24415.map Setup.Block.length).sum = source24415.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column4.Chunk190
