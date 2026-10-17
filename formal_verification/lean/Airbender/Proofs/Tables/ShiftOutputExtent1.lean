import Airbender.Proofs.Tables.LiteralSizes
import Airbender.Proofs.Tables.ShiftOutputPartitions1
import Airbender.Proofs.Tables.ImportedBlocks
namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output1_extent0 :
    (output1Blocks0.toList.map Block.length).sum = 17682 := by
  dsimp only [output1Blocks0]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent1 :
    (output1Blocks1.toList.map Block.length).sum = 14920 := by
  dsimp only [output1Blocks1]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent2 :
    (output1Blocks2.toList.map Block.length).sum = 14064 := by
  dsimp only [output1Blocks2]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent3 :
    (output1Blocks3.toList.map Block.length).sum = 14056 := by
  dsimp only [output1Blocks3]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent4 :
    (output1Blocks4.toList.map Block.length).sum = 22762 := by
  dsimp only [output1Blocks4]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent5 :
    (output1Blocks5.toList.map Block.length).sum = 25376 := by
  dsimp only [output1Blocks5]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent6 :
    (output1Blocks6.toList.map Block.length).sum = 24522 := by
  dsimp only [output1Blocks6]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent7 :
    (output1Blocks7.toList.map Block.length).sum = 15446 := by
  dsimp only [output1Blocks7]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent8 :
    (output1Blocks8.toList.map Block.length).sum = 14040 := by
  dsimp only [output1Blocks8]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent9 :
    (output1Blocks9.toList.map Block.length).sum = 13096 := by
  dsimp only [output1Blocks9]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent10 :
    (output1Blocks10.toList.map Block.length).sum = 13088 := by
  dsimp only [output1Blocks10]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent11 :
    (output1Blocks11.toList.map Block.length).sum = 15920 := by
  dsimp only [output1Blocks11]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent12 :
    (output1Blocks12.toList.map Block.length).sum = 15784 := by
  dsimp only [output1Blocks12]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent13 :
    (output1Blocks13.toList.map Block.length).sum = 14392 := by
  dsimp only [output1Blocks13]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent14 :
    (output1Blocks14.toList.map Block.length).sum = 13550 := by
  dsimp only [output1Blocks14]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_extent15 :
    (output1Blocks15.toList.map Block.length).sum = 13446 := by
  dsimp only [output1Blocks15]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem output1_coverage :
    (byteShiftColumn5.blocks.toList.map Block.length).sum = 262144 := by
  have joined : byteShiftColumn5.blocks = ((((output1Blocks0 ++ output1Blocks1) ++ (output1Blocks2 ++ output1Blocks3)) ++ ((output1Blocks4 ++ output1Blocks5) ++ (output1Blocks6 ++ output1Blocks7))) ++ (((output1Blocks8 ++ output1Blocks9) ++ (output1Blocks10 ++ output1Blocks11)) ++ ((output1Blocks12 ++ output1Blocks13) ++ (output1Blocks14 ++ output1Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, List.map_append, List.sum_append,
    output1_extent0, output1_extent1, output1_extent2, output1_extent3, output1_extent4, output1_extent5, output1_extent6, output1_extent7, output1_extent8, output1_extent9, output1_extent10, output1_extent11, output1_extent12, output1_extent13, output1_extent14, output1_extent15, Nat.reduceAdd]

end Airbender.Verification.ShiftCertificate
