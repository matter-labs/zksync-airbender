import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ShiftOutputPartitions2
import Airbender.Proofs.Tables.ImportedBlocks
namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output2_extent0 :
    (output2Blocks0.toList.map Block.length).sum = 17522 := by
  dsimp only [output2Blocks0]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent1 :
    (output2Blocks1.toList.map Block.length).sum = 14864 := by
  dsimp only [output2Blocks1]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent2 :
    (output2Blocks2.toList.map Block.length).sum = 13864 := by
  dsimp only [output2Blocks2]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent3 :
    (output2Blocks3.toList.map Block.length).sum = 13992 := by
  dsimp only [output2Blocks3]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent4 :
    (output2Blocks4.toList.map Block.length).sum = 15624 := by
  dsimp only [output2Blocks4]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent5 :
    (output2Blocks5.toList.map Block.length).sum = 14304 := by
  dsimp only [output2Blocks5]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent6 :
    (output2Blocks6.toList.map Block.length).sum = 13864 := by
  dsimp only [output2Blocks6]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent7 :
    (output2Blocks7.toList.map Block.length).sum = 13992 := by
  dsimp only [output2Blocks7]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent8 :
    (output2Blocks8.toList.map Block.length).sum = 14616 := by
  dsimp only [output2Blocks8]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent9 :
    (output2Blocks9.toList.map Block.length).sum = 26594 := by
  dsimp only [output2Blocks9]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent10 :
    (output2Blocks10.toList.map Block.length).sum = 24576 := by
  dsimp only [output2Blocks10]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent11 :
    (output2Blocks11.toList.map Block.length).sum = 21816 := by
  dsimp only [output2Blocks11]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent12 :
    (output2Blocks12.toList.map Block.length).sum = 15400 := by
  dsimp only [output2Blocks12]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent13 :
    (output2Blocks13.toList.map Block.length).sum = 14318 := by
  dsimp only [output2Blocks13]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent14 :
    (output2Blocks14.toList.map Block.length).sum = 13352 := by
  dsimp only [output2Blocks14]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_extent15 :
    (output2Blocks15.toList.map Block.length).sum = 13446 := by
  dsimp only [output2Blocks15]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output2_coverage :
    (byteShiftColumn6.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn6.blocks = ((((output2Blocks0 ++ output2Blocks1) ++ (output2Blocks2 ++ output2Blocks3)) ++ ((output2Blocks4 ++ output2Blocks5) ++ (output2Blocks6 ++ output2Blocks7))) ++ (((output2Blocks8 ++ output2Blocks9) ++ (output2Blocks10 ++ output2Blocks11)) ++ ((output2Blocks12 ++ output2Blocks13) ++ (output2Blocks14 ++ output2Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append,
    output2_extent0, output2_extent1, output2_extent2, output2_extent3, output2_extent4, output2_extent5, output2_extent6, output2_extent7, output2_extent8, output2_extent9, output2_extent10, output2_extent11, output2_extent12, output2_extent13, output2_extent14, output2_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
