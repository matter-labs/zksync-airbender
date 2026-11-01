import Airbender.Proofs.Tables.ShiftExtentChecks2
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem output2_extent0 : (output2Blocks0.toList.map Block.length).sum = 17522 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding0]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨0, by decide +kernel⟩

theorem output2_extent1 : (output2Blocks1.toList.map Block.length).sum = 14864 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding1]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨1, by decide +kernel⟩

theorem output2_extent2 : (output2Blocks2.toList.map Block.length).sum = 13864 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding2]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨2, by decide +kernel⟩

theorem output2_extent3 : (output2Blocks3.toList.map Block.length).sum = 13992 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding3]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨3, by decide +kernel⟩

theorem output2_extent4 : (output2Blocks4.toList.map Block.length).sum = 15624 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding4]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨4, by decide +kernel⟩

theorem output2_extent5 : (output2Blocks5.toList.map Block.length).sum = 14304 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding5]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨5, by decide +kernel⟩

theorem output2_extent6 : (output2Blocks6.toList.map Block.length).sum = 13864 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding6]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨6, by decide +kernel⟩

theorem output2_extent7 : (output2Blocks7.toList.map Block.length).sum = 13992 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding7]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨7, by decide +kernel⟩

theorem output2_extent8 : (output2Blocks8.toList.map Block.length).sum = 14616 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding8]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨8, by decide +kernel⟩

theorem output2_extent9 : (output2Blocks9.toList.map Block.length).sum = 26594 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding9]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨9, by decide +kernel⟩

theorem output2_extent10 : (output2Blocks10.toList.map Block.length).sum = 24576 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding10]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨10, by decide +kernel⟩

theorem output2_extent11 : (output2Blocks11.toList.map Block.length).sum = 21816 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding11]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨11, by decide +kernel⟩

theorem output2_extent12 : (output2Blocks12.toList.map Block.length).sum = 15400 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding12]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨12, by decide +kernel⟩

theorem output2_extent13 : (output2Blocks13.toList.map Block.length).sum = 14318 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding13]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨13, by decide +kernel⟩

theorem output2_extent14 : (output2Blocks14.toList.map Block.length).sum = 13352 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding14]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨14, by decide +kernel⟩

theorem output2_extent15 : (output2Blocks15.toList.map Block.length).sum = 13446 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane2.binding15]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane2.requests Airbender.Verification.ShiftExtentChecks.Lane2.checked ⟨15, by decide +kernel⟩

theorem output2_coverage : (byteShiftColumn6.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn6.blocks = ((((output2Blocks0 ++ output2Blocks1) ++ (output2Blocks2 ++ output2Blocks3)) ++ ((output2Blocks4 ++ output2Blocks5) ++ (output2Blocks6 ++ output2Blocks7))) ++ (((output2Blocks8 ++ output2Blocks9) ++ (output2Blocks10 ++ output2Blocks11)) ++ ((output2Blocks12 ++ output2Blocks13) ++ (output2Blocks14 ++ output2Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append, output2_extent0, output2_extent1, output2_extent2, output2_extent3, output2_extent4, output2_extent5, output2_extent6, output2_extent7, output2_extent8, output2_extent9, output2_extent10, output2_extent11, output2_extent12, output2_extent13, output2_extent14, output2_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
