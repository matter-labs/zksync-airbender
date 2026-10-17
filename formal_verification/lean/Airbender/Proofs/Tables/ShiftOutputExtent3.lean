import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ShiftOutputPartitions3
import Airbender.Proofs.Tables.ImportedBlocks
namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output3_extent0 :
    (output3Blocks0.toList.map Block.length).sum = 16537 := by
  dsimp only [output3Blocks0]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent1 :
    (output3Blocks1.toList.map Block.length).sum = 14096 := by
  dsimp only [output3Blocks1]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent2 :
    (output3Blocks2.toList.map Block.length).sum = 13312 := by
  dsimp only [output3Blocks2]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent3 :
    (output3Blocks3.toList.map Block.length).sum = 13088 := by
  dsimp only [output3Blocks3]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent4 :
    (output3Blocks4.toList.map Block.length).sum = 15552 := by
  dsimp only [output3Blocks4]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent5 :
    (output3Blocks5.toList.map Block.length).sum = 15912 := by
  dsimp only [output3Blocks5]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent6 :
    (output3Blocks6.toList.map Block.length).sum = 14824 := by
  dsimp only [output3Blocks6]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent7 :
    (output3Blocks7.toList.map Block.length).sum = 14080 := by
  dsimp only [output3Blocks7]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent8 :
    (output3Blocks8.toList.map Block.length).sum = 14536 := by
  dsimp only [output3Blocks8]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent9 :
    (output3Blocks9.toList.map Block.length).sum = 17168 := by
  dsimp only [output3Blocks9]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent10 :
    (output3Blocks10.toList.map Block.length).sum = 15272 := by
  dsimp only [output3Blocks10]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent11 :
    (output3Blocks11.toList.map Block.length).sum = 14072 := by
  dsimp only [output3Blocks11]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent12 :
    (output3Blocks12.toList.map Block.length).sum = 13928 := by
  dsimp only [output3Blocks12]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent13 :
    (output3Blocks13.toList.map Block.length).sum = 23688 := by
  dsimp only [output3Blocks13]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent14 :
    (output3Blocks14.toList.map Block.length).sum = 24088 := by
  dsimp only [output3Blocks14]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_extent15 :
    (output3Blocks15.toList.map Block.length).sum = 21991 := by
  dsimp only [output3Blocks15]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output3_coverage :
    (byteShiftColumn7.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn7.blocks = ((((output3Blocks0 ++ output3Blocks1) ++ (output3Blocks2 ++ output3Blocks3)) ++ ((output3Blocks4 ++ output3Blocks5) ++ (output3Blocks6 ++ output3Blocks7))) ++ (((output3Blocks8 ++ output3Blocks9) ++ (output3Blocks10 ++ output3Blocks11)) ++ ((output3Blocks12 ++ output3Blocks13) ++ (output3Blocks14 ++ output3Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append,
    output3_extent0, output3_extent1, output3_extent2, output3_extent3, output3_extent4, output3_extent5, output3_extent6, output3_extent7, output3_extent8, output3_extent9, output3_extent10, output3_extent11, output3_extent12, output3_extent13, output3_extent14, output3_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
