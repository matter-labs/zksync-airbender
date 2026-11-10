import Airbender.Proofs.Tables.ShiftExtentChecks1
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem output1_extent0 : (output1Blocks0.toList.map Block.length).sum = 17682 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding0]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨0, by decide +kernel⟩

theorem output1_extent1 : (output1Blocks1.toList.map Block.length).sum = 14920 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding1]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨1, by decide +kernel⟩

theorem output1_extent2 : (output1Blocks2.toList.map Block.length).sum = 14064 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding2]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨2, by decide +kernel⟩

theorem output1_extent3 : (output1Blocks3.toList.map Block.length).sum = 14056 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding3]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨3, by decide +kernel⟩

theorem output1_extent4 : (output1Blocks4.toList.map Block.length).sum = 22762 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding4]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨4, by decide +kernel⟩

theorem output1_extent5 : (output1Blocks5.toList.map Block.length).sum = 25376 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding5]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨5, by decide +kernel⟩

theorem output1_extent6 : (output1Blocks6.toList.map Block.length).sum = 24522 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding6]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨6, by decide +kernel⟩

theorem output1_extent7 : (output1Blocks7.toList.map Block.length).sum = 15446 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding7]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨7, by decide +kernel⟩

theorem output1_extent8 : (output1Blocks8.toList.map Block.length).sum = 14040 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding8]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨8, by decide +kernel⟩

theorem output1_extent9 : (output1Blocks9.toList.map Block.length).sum = 13096 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding9]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨9, by decide +kernel⟩

theorem output1_extent10 : (output1Blocks10.toList.map Block.length).sum = 13088 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding10]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨10, by decide +kernel⟩

theorem output1_extent11 : (output1Blocks11.toList.map Block.length).sum = 15920 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding11]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨11, by decide +kernel⟩

theorem output1_extent12 : (output1Blocks12.toList.map Block.length).sum = 15784 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding12]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨12, by decide +kernel⟩

theorem output1_extent13 : (output1Blocks13.toList.map Block.length).sum = 14392 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding13]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨13, by decide +kernel⟩

theorem output1_extent14 : (output1Blocks14.toList.map Block.length).sum = 13550 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding14]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨14, by decide +kernel⟩

theorem output1_extent15 : (output1Blocks15.toList.map Block.length).sum = 13446 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane1.binding15]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane1.requests Airbender.Verification.ShiftExtentChecks.Lane1.checked ⟨15, by decide +kernel⟩

theorem output1_coverage : (byteShiftColumn5.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn5.blocks = ((((output1Blocks0 ++ output1Blocks1) ++ (output1Blocks2 ++ output1Blocks3)) ++ ((output1Blocks4 ++ output1Blocks5) ++ (output1Blocks6 ++ output1Blocks7))) ++ (((output1Blocks8 ++ output1Blocks9) ++ (output1Blocks10 ++ output1Blocks11)) ++ ((output1Blocks12 ++ output1Blocks13) ++ (output1Blocks14 ++ output1Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append, output1_extent0, output1_extent1, output1_extent2, output1_extent3, output1_extent4, output1_extent5, output1_extent6, output1_extent7, output1_extent8, output1_extent9, output1_extent10, output1_extent11, output1_extent12, output1_extent13, output1_extent14, output1_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
