import GKRProtocol.UnifiedSpecialParts.Column2.Chunk0.Foundation

namespace Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def source0 : Setup.Block := original.get ⟨0, by decide +kernel⟩

column_blocks_part part0_0 from (UnifiedReduced.Setup.nativeZeroData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def destination0_0 : Setup.Block := part0_0.get ⟨0, by decide +kernel⟩

column_blocks_part part0_1 from (UnifiedReduced.Setup.nativeRegisterZeroData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def destination0_1 : Setup.Block := part0_1.get ⟨0, by decide +kernel⟩

column_blocks_part part0_2 from (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def destination0_2 : Setup.Block := part0_2.get ⟨0, by decide +kernel⟩

noncomputable def target0 : List Setup.Block := part0_0 ++ part0_1 ++ part0_2

theorem follows0 : blockTargetsFollow source0 0 target0 :=
  And.intro (by
    intro index bounded
    change source0.get? (0 + index) = destination0_0.get? index
    change (Setup.Block.affine 131077 0 0).get? (0 + index) = (Setup.Block.affine 1 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 1 := bounded; omega : 0 + index < 131077)
    · exact (show index < 1 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (1 + index) = destination0_1.get? index
    change (Setup.Block.affine 131077 0 0).get? (1 + index) = (Setup.Block.affine 131072 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 131072 := bounded; omega : 1 + index < 131077)
    · exact (show index < 131072 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source0.get? (131073 + index) = destination0_2.get? index
    change (Setup.Block.affine 131077 0 0).get? (131073 + index) = (Setup.Block.affine 4 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 4 := bounded; omega : 131073 + index < 131077)
    · exact (show index < 4 from bounded)
    · decide +kernel
  ) (True.intro)))

theorem length0 : (target0.map Setup.Block.length).sum = source0.length := by decide +kernel

noncomputable def source1 : Setup.Block := original.get ⟨1, by decide +kernel⟩

column_blocks_part part1_0 from (UnifiedReduced.Setup.nativeCleanupData.columns[(2 : Nat)]) start 1 stop 2
noncomputable def destination1_0 : Setup.Block := part1_0.get ⟨0, by decide +kernel⟩

noncomputable def target1 : List Setup.Block := part1_0

theorem follows1 : blockTargetsFollow source1 0 target1 :=
  And.intro (by
    intro index bounded
    change source1.get? (0 + index) = destination1_0.get? index
    have same : source1 = destination1_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length1 : (target1.map Setup.Block.length).sum = source1.length := by decide +kernel

noncomputable def source2 : Setup.Block := original.get ⟨2, by decide +kernel⟩

column_blocks_part part2_0 from (UnifiedReduced.Setup.nativeByteSignData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def destination2_0 : Setup.Block := part2_0.get ⟨0, by decide +kernel⟩

column_blocks_part part2_1 from (UnifiedReduced.Setup.nativeSignData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def destination2_1 : Setup.Block := part2_1.get ⟨0, by decide +kernel⟩

column_blocks_part part2_2 from (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]) start 0 stop 1
noncomputable def destination2_2 : Setup.Block := part2_2.get ⟨0, by decide +kernel⟩

noncomputable def target2 : List Setup.Block := part2_0 ++ part2_1 ++ part2_2

theorem follows2 : blockTargetsFollow source2 0 target2 :=
  And.intro (by
    intro index bounded
    change source2.get? (0 + index) = destination2_0.get? index
    change (Setup.Block.affine 66048 0 0).get? (0 + index) = (Setup.Block.affine 256 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 256 := bounded; omega : 0 + index < 66048)
    · exact (show index < 256 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (256 + index) = destination2_1.get? index
    change (Setup.Block.affine 66048 0 0).get? (256 + index) = (Setup.Block.affine 65536 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 65536 := bounded; omega : 256 + index < 66048)
    · exact (show index < 65536 from bounded)
    · decide +kernel
  ) (And.intro (by
    intro index bounded
    change source2.get? (65792 + index) = destination2_2.get? index
    change (Setup.Block.affine 66048 0 0).get? (65792 + index) = (Setup.Block.affine 256 0 0).get? index
    apply affine_block_span
    · exact (by have bound : index < 256 := bounded; omega : 65792 + index < 66048)
    · exact (show index < 256 from bounded)
    · decide +kernel
  ) (True.intro)))

theorem length2 : (target2.map Setup.Block.length).sum = source2.length := by decide +kernel

noncomputable def source3 : Setup.Block := original.get ⟨3, by decide +kernel⟩

column_blocks_part part3_0 from (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]) start 1 stop 2
noncomputable def destination3_0 : Setup.Block := part3_0.get ⟨0, by decide +kernel⟩

noncomputable def target3 : List Setup.Block := part3_0

theorem follows3 : blockTargetsFollow source3 0 target3 :=
  And.intro (by
    intro index bounded
    change source3.get? (0 + index) = destination3_0.get? index
    have same : source3 = destination3_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length3 : (target3.map Setup.Block.length).sum = source3.length := by decide +kernel

noncomputable def source4 : Setup.Block := original.get ⟨4, by decide +kernel⟩

column_blocks_part part4_0 from (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]) start 2 stop 3
noncomputable def destination4_0 : Setup.Block := part4_0.get ⟨0, by decide +kernel⟩

noncomputable def target4 : List Setup.Block := part4_0

theorem follows4 : blockTargetsFollow source4 0 target4 :=
  And.intro (by
    intro index bounded
    change source4.get? (0 + index) = destination4_0.get? index
    have same : source4 = destination4_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length4 : (target4.map Setup.Block.length).sum = source4.length := by decide +kernel

noncomputable def source5 : Setup.Block := original.get ⟨5, by decide +kernel⟩

column_blocks_part part5_0 from (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]) start 3 stop 4
noncomputable def destination5_0 : Setup.Block := part5_0.get ⟨0, by decide +kernel⟩

noncomputable def target5 : List Setup.Block := part5_0

theorem follows5 : blockTargetsFollow source5 0 target5 :=
  And.intro (by
    intro index bounded
    change source5.get? (0 + index) = destination5_0.get? index
    have same : source5 = destination5_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length5 : (target5.map Setup.Block.length).sum = source5.length := by decide +kernel

noncomputable def source6 : Setup.Block := original.get ⟨6, by decide +kernel⟩

column_blocks_part part6_0 from (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]) start 4 stop 5
noncomputable def destination6_0 : Setup.Block := part6_0.get ⟨0, by decide +kernel⟩

noncomputable def target6 : List Setup.Block := part6_0

theorem follows6 : blockTargetsFollow source6 0 target6 :=
  And.intro (by
    intro index bounded
    change source6.get? (0 + index) = destination6_0.get? index
    have same : source6 = destination6_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length6 : (target6.map Setup.Block.length).sum = source6.length := by decide +kernel

noncomputable def source7 : Setup.Block := original.get ⟨7, by decide +kernel⟩

column_blocks_part part7_0 from (UnifiedReduced.Setup.nativeTruncationData.columns[(2 : Nat)]) start 5 stop 6
noncomputable def destination7_0 : Setup.Block := part7_0.get ⟨0, by decide +kernel⟩

noncomputable def target7 : List Setup.Block := part7_0

theorem follows7 : blockTargetsFollow source7 0 target7 :=
  And.intro (by
    intro index bounded
    change source7.get? (0 + index) = destination7_0.get? index
    have same : source7 = destination7_0 := by rfl
    rw [same, Nat.zero_add]
  ) (True.intro)

theorem length7 : (target7.map Setup.Block.length).sum = source7.length := by decide +kernel

end Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0
