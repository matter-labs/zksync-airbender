import Airbender.Proofs.GKRProtocol.UnifiedSpecialParts.Column5.Chunk191.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source24536 : Setup.Block := original.get ⟨88, by decide +kernel⟩

column_blocks_part part24536_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24536 stop 24537
noncomputable def destination24536_0 : Setup.Block := part24536_0.get ⟨0, by decide +kernel⟩

noncomputable def target24536 : List Setup.Block := part24536_0

theorem follows24536 : blockTargetsFollow source24536 0 target24536 :=
  And.intro (by
    intro index bounded
    change source24536.get? (0 + index) = destination24536_0.get? index
    have same : source24536 = destination24536_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24536 : (target24536.map Setup.Block.length).sum = source24536.length := by decide +kernel

noncomputable def source24537 : Setup.Block := original.get ⟨89, by decide +kernel⟩

column_blocks_part part24537_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24537 stop 24538
noncomputable def destination24537_0 : Setup.Block := part24537_0.get ⟨0, by decide +kernel⟩

noncomputable def target24537 : List Setup.Block := part24537_0

theorem follows24537 : blockTargetsFollow source24537 0 target24537 :=
  And.intro (by
    intro index bounded
    change source24537.get? (0 + index) = destination24537_0.get? index
    have same : source24537 = destination24537_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24537 : (target24537.map Setup.Block.length).sum = source24537.length := by decide +kernel

noncomputable def source24538 : Setup.Block := original.get ⟨90, by decide +kernel⟩

column_blocks_part part24538_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24538 stop 24539
noncomputable def destination24538_0 : Setup.Block := part24538_0.get ⟨0, by decide +kernel⟩

noncomputable def target24538 : List Setup.Block := part24538_0

theorem follows24538 : blockTargetsFollow source24538 0 target24538 :=
  And.intro (by
    intro index bounded
    change source24538.get? (0 + index) = destination24538_0.get? index
    have same : source24538 = destination24538_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24538 : (target24538.map Setup.Block.length).sum = source24538.length := by decide +kernel

noncomputable def source24539 : Setup.Block := original.get ⟨91, by decide +kernel⟩

column_blocks_part part24539_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24539 stop 24540
noncomputable def destination24539_0 : Setup.Block := part24539_0.get ⟨0, by decide +kernel⟩

noncomputable def target24539 : List Setup.Block := part24539_0

theorem follows24539 : blockTargetsFollow source24539 0 target24539 :=
  And.intro (by
    intro index bounded
    change source24539.get? (0 + index) = destination24539_0.get? index
    have same : source24539 = destination24539_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24539 : (target24539.map Setup.Block.length).sum = source24539.length := by decide +kernel

noncomputable def source24540 : Setup.Block := original.get ⟨92, by decide +kernel⟩

column_blocks_part part24540_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24540 stop 24541
noncomputable def destination24540_0 : Setup.Block := part24540_0.get ⟨0, by decide +kernel⟩

noncomputable def target24540 : List Setup.Block := part24540_0

theorem follows24540 : blockTargetsFollow source24540 0 target24540 :=
  And.intro (by
    intro index bounded
    change source24540.get? (0 + index) = destination24540_0.get? index
    have same : source24540 = destination24540_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24540 : (target24540.map Setup.Block.length).sum = source24540.length := by decide +kernel

noncomputable def source24541 : Setup.Block := original.get ⟨93, by decide +kernel⟩

column_blocks_part part24541_0 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24541 stop 24542
noncomputable def destination24541_0 : Setup.Block := part24541_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24541_1 from (UnifiedReduced.Setup.nativeShiftData.columns[(5 : Nat)]) start 24542 stop 24543
noncomputable def destination24541_1 : Setup.Block := part24541_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24541_2 from (UnifiedReduced.Setup.nativeROMData.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination24541_2 : Setup.Block := part24541_2.get ⟨0, by decide +kernel⟩

noncomputable def target24541 : List Setup.Block := part24541_0 ++ part24541_1 ++ part24541_2

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

noncomputable def source24542 : Setup.Block := original.get ⟨94, by decide +kernel⟩

column_blocks_part part24542_0 from (UnifiedReduced.Setup.nativeROMData.columns[(5 : Nat)]) start 1 stop 2
noncomputable def destination24542_0 : Setup.Block := part24542_0.get ⟨0, by decide +kernel⟩

column_blocks_part part24542_1 from (UnifiedReduced.Setup.nativeRotate16Data.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination24542_1 : Setup.Block := part24542_1.get ⟨0, by decide +kernel⟩

column_blocks_part part24542_2 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 0 stop 1
noncomputable def destination24542_2 : Setup.Block := part24542_2.get ⟨0, by decide +kernel⟩

noncomputable def target24542 : List Setup.Block := part24542_0 ++ part24542_1 ++ part24542_2

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

noncomputable def source24543 : Setup.Block := original.get ⟨95, by decide +kernel⟩

column_blocks_part part24543_0 from (UnifiedReduced.Setup.nativeRotate12Data.columns[(5 : Nat)]) start 1 stop 2
noncomputable def destination24543_0 : Setup.Block := part24543_0.get ⟨0, by decide +kernel⟩

noncomputable def target24543 : List Setup.Block := part24543_0

theorem follows24543 : blockTargetsFollow source24543 0 target24543 :=
  And.intro (by
    intro index bounded
    change source24543.get? (0 + index) = destination24543_0.get? index
    have same : source24543 = destination24543_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length24543 : (target24543.map Setup.Block.length).sum = source24543.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191
