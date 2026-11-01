import Airbender.Proofs.Tables.ShiftExtentChecks0
import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ImportedBlocks

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Verification
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem output0_extent0 : (output0Blocks0.toList.map Block.length).sum = 26881 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding0]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨0, by decide +kernel⟩

theorem output0_extent1 : (output0Blocks1.toList.map Block.length).sum = 24624 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding1]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨1, by decide +kernel⟩

theorem output0_extent2 : (output0Blocks2.toList.map Block.length).sum = 22497 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding2]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨2, by decide +kernel⟩

theorem output0_extent3 : (output0Blocks3.toList.map Block.length).sum = 15448 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding3]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨3, by decide +kernel⟩

theorem output0_extent4 : (output0Blocks4.toList.map Block.length).sum = 14600 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding4]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨4, by decide +kernel⟩

theorem output0_extent5 : (output0Blocks5.toList.map Block.length).sum = 14016 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding5]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨5, by decide +kernel⟩

theorem output0_extent6 : (output0Blocks6.toList.map Block.length).sum = 14680 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding6]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨6, by decide +kernel⟩

theorem output0_extent7 : (output0Blocks7.toList.map Block.length).sum = 16904 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding7]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨7, by decide +kernel⟩

theorem output0_extent8 : (output0Blocks8.toList.map Block.length).sum = 15040 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding8]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨8, by decide +kernel⟩

theorem output0_extent9 : (output0Blocks9.toList.map Block.length).sum = 13864 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding9]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨9, by decide +kernel⟩

theorem output0_extent10 : (output0Blocks10.toList.map Block.length).sum = 13864 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding10]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨10, by decide +kernel⟩

theorem output0_extent11 : (output0Blocks11.toList.map Block.length).sum = 16120 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding11]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨11, by decide +kernel⟩

theorem output0_extent12 : (output0Blocks12.toList.map Block.length).sum = 14168 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding12]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨12, by decide +kernel⟩

theorem output0_extent13 : (output0Blocks13.toList.map Block.length).sum = 13528 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding13]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨13, by decide +kernel⟩

theorem output0_extent14 : (output0Blocks14.toList.map Block.length).sum = 13032 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding14]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨14, by decide +kernel⟩

theorem output0_extent15 : (output0Blocks15.toList.map Block.length).sum = 12878 := by
  rw [← Airbender.Verification.ShiftExtentChecks.Lane0.binding15]
  exact PackedLengthChecks.check_sound_at Airbender.Verification.ShiftExtentChecks.Lane0.requests Airbender.Verification.ShiftExtentChecks.Lane0.checked ⟨15, by decide +kernel⟩

theorem output0_coverage : (byteShiftColumn4.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn4.blocks = ((((output0Blocks0 ++ output0Blocks1) ++ (output0Blocks2 ++ output0Blocks3)) ++ ((output0Blocks4 ++ output0Blocks5) ++ (output0Blocks6 ++ output0Blocks7))) ++ (((output0Blocks8 ++ output0Blocks9) ++ (output0Blocks10 ++ output0Blocks11)) ++ ((output0Blocks12 ++ output0Blocks13) ++ (output0Blocks14 ++ output0Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append, output0_extent0, output0_extent1, output0_extent2, output0_extent3, output0_extent4, output0_extent5, output0_extent6, output0_extent7, output0_extent8, output0_extent9, output0_extent10, output0_extent11, output0_extent12, output0_extent13, output0_extent14, output0_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
