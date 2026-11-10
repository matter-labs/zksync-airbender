import Airbender.Proofs.Tables.ShiftExtentChecks3
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem output3_extent0 : (output3Blocks0.toList.map Block.length).sum = 16537 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding0]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨0, by decide +kernel⟩

theorem output3_extent1 : (output3Blocks1.toList.map Block.length).sum = 14096 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding1]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨1, by decide +kernel⟩

theorem output3_extent2 : (output3Blocks2.toList.map Block.length).sum = 13312 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding2]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨2, by decide +kernel⟩

theorem output3_extent3 : (output3Blocks3.toList.map Block.length).sum = 13088 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding3]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨3, by decide +kernel⟩

theorem output3_extent4 : (output3Blocks4.toList.map Block.length).sum = 15552 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding4]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨4, by decide +kernel⟩

theorem output3_extent5 : (output3Blocks5.toList.map Block.length).sum = 15912 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding5]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨5, by decide +kernel⟩

theorem output3_extent6 : (output3Blocks6.toList.map Block.length).sum = 14824 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding6]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨6, by decide +kernel⟩

theorem output3_extent7 : (output3Blocks7.toList.map Block.length).sum = 14080 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding7]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨7, by decide +kernel⟩

theorem output3_extent8 : (output3Blocks8.toList.map Block.length).sum = 14536 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding8]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨8, by decide +kernel⟩

theorem output3_extent9 : (output3Blocks9.toList.map Block.length).sum = 17168 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding9]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨9, by decide +kernel⟩

theorem output3_extent10 : (output3Blocks10.toList.map Block.length).sum = 15272 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding10]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨10, by decide +kernel⟩

theorem output3_extent11 : (output3Blocks11.toList.map Block.length).sum = 14072 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding11]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨11, by decide +kernel⟩

theorem output3_extent12 : (output3Blocks12.toList.map Block.length).sum = 13928 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding12]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨12, by decide +kernel⟩

theorem output3_extent13 : (output3Blocks13.toList.map Block.length).sum = 23688 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding13]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨13, by decide +kernel⟩

theorem output3_extent14 : (output3Blocks14.toList.map Block.length).sum = 24088 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding14]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨14, by decide +kernel⟩

theorem output3_extent15 : (output3Blocks15.toList.map Block.length).sum = 21991 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane3.binding15]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane3.requests Airbender.Verification.ShiftExtentChecks.Lane3.checked ⟨15, by decide +kernel⟩

theorem output3_coverage : (byteShiftColumn7.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn7.blocks = ((((output3Blocks0 ++ output3Blocks1) ++ (output3Blocks2 ++ output3Blocks3)) ++ ((output3Blocks4 ++ output3Blocks5) ++ (output3Blocks6 ++ output3Blocks7))) ++ (((output3Blocks8 ++ output3Blocks9) ++ (output3Blocks10 ++ output3Blocks11)) ++ ((output3Blocks12 ++ output3Blocks13) ++ (output3Blocks14 ++ output3Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append, output3_extent0, output3_extent1, output3_extent2, output3_extent3, output3_extent4, output3_extent5, output3_extent6, output3_extent7, output3_extent8, output3_extent9, output3_extent10, output3_extent11, output3_extent12, output3_extent13, output3_extent14, output3_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
