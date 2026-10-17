import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ShiftOutputPartitions0
import Airbender.Proofs.Tables.ImportedBlocks
namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output0_extent0 :
    (output0Blocks0.toList.map Block.length).sum = 26881 := by
  dsimp only [output0Blocks0]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent1 :
    (output0Blocks1.toList.map Block.length).sum = 24624 := by
  dsimp only [output0Blocks1]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent2 :
    (output0Blocks2.toList.map Block.length).sum = 22497 := by
  dsimp only [output0Blocks2]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent3 :
    (output0Blocks3.toList.map Block.length).sum = 15448 := by
  dsimp only [output0Blocks3]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent4 :
    (output0Blocks4.toList.map Block.length).sum = 14600 := by
  dsimp only [output0Blocks4]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent5 :
    (output0Blocks5.toList.map Block.length).sum = 14016 := by
  dsimp only [output0Blocks5]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent6 :
    (output0Blocks6.toList.map Block.length).sum = 14680 := by
  dsimp only [output0Blocks6]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent7 :
    (output0Blocks7.toList.map Block.length).sum = 16904 := by
  dsimp only [output0Blocks7]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent8 :
    (output0Blocks8.toList.map Block.length).sum = 15040 := by
  dsimp only [output0Blocks8]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent9 :
    (output0Blocks9.toList.map Block.length).sum = 13864 := by
  dsimp only [output0Blocks9]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent10 :
    (output0Blocks10.toList.map Block.length).sum = 13864 := by
  dsimp only [output0Blocks10]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent11 :
    (output0Blocks11.toList.map Block.length).sum = 16120 := by
  dsimp only [output0Blocks11]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent12 :
    (output0Blocks12.toList.map Block.length).sum = 14168 := by
  dsimp only [output0Blocks12]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent13 :
    (output0Blocks13.toList.map Block.length).sum = 13528 := by
  dsimp only [output0Blocks13]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent14 :
    (output0Blocks14.toList.map Block.length).sum = 13032 := by
  dsimp only [output0Blocks14]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_extent15 :
    (output0Blocks15.toList.map Block.length).sum = 12878 := by
  dsimp only [output0Blocks15]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output0_coverage :
    (byteShiftColumn4.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn4.blocks = ((((output0Blocks0 ++ output0Blocks1) ++ (output0Blocks2 ++ output0Blocks3)) ++ ((output0Blocks4 ++ output0Blocks5) ++ (output0Blocks6 ++ output0Blocks7))) ++ (((output0Blocks8 ++ output0Blocks9) ++ (output0Blocks10 ++ output0Blocks11)) ++ ((output0Blocks12 ++ output0Blocks13) ++ (output0Blocks14 ++ output0Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append,
    output0_extent0, output0_extent1, output0_extent2, output0_extent3, output0_extent4, output0_extent5, output0_extent6, output0_extent7, output0_extent8, output0_extent9, output0_extent10, output0_extent11, output0_extent12, output0_extent13, output0_extent14, output0_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
