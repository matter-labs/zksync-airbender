import Airbender.Proofs.Blake2Round.Carry8Partitions

namespace Airbender.Blake2Round.Proofs.Carry8Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Sizes of the actual imported partitions, checked separately from their values. -/
theorem extent0 :
    (carry8ColumnBlocks0.toList.map Block.length).sum = carry8ColumnSize0 := by
  dsimp only [carry8ColumnBlocks0, carry8ColumnSize0]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent1 :
    (carry8ColumnBlocks1.toList.map Block.length).sum = carry8ColumnSize1 := by
  dsimp only [carry8ColumnBlocks1, carry8ColumnSize1]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent2 :
    (carry8ColumnBlocks2.toList.map Block.length).sum = carry8ColumnSize2 := by
  dsimp only [carry8ColumnBlocks2, carry8ColumnSize2]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent3 :
    (carry8ColumnBlocks3.toList.map Block.length).sum = carry8ColumnSize3 := by
  dsimp only [carry8ColumnBlocks3, carry8ColumnSize3]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent4 :
    (carry8ColumnBlocks4.toList.map Block.length).sum = carry8ColumnSize4 := by
  dsimp only [carry8ColumnBlocks4, carry8ColumnSize4]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent5 :
    (carry8ColumnBlocks5.toList.map Block.length).sum = carry8ColumnSize5 := by
  dsimp only [carry8ColumnBlocks5, carry8ColumnSize5]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent6 :
    (carry8ColumnBlocks6.toList.map Block.length).sum = carry8ColumnSize6 := by
  dsimp only [carry8ColumnBlocks6, carry8ColumnSize6]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent7 :
    (carry8ColumnBlocks7.toList.map Block.length).sum = carry8ColumnSize7 := by
  dsimp only [carry8ColumnBlocks7, carry8ColumnSize7]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent8 :
    (carry8ColumnBlocks8.toList.map Block.length).sum = carry8ColumnSize8 := by
  dsimp only [carry8ColumnBlocks8, carry8ColumnSize8]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent9 :
    (carry8ColumnBlocks9.toList.map Block.length).sum = carry8ColumnSize9 := by
  dsimp only [carry8ColumnBlocks9, carry8ColumnSize9]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent10 :
    (carry8ColumnBlocks10.toList.map Block.length).sum = carry8ColumnSize10 := by
  dsimp only [carry8ColumnBlocks10, carry8ColumnSize10]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent11 :
    (carry8ColumnBlocks11.toList.map Block.length).sum = carry8ColumnSize11 := by
  dsimp only [carry8ColumnBlocks11, carry8ColumnSize11]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent12 :
    (carry8ColumnBlocks12.toList.map Block.length).sum = carry8ColumnSize12 := by
  dsimp only [carry8ColumnBlocks12, carry8ColumnSize12]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent13 :
    (carry8ColumnBlocks13.toList.map Block.length).sum = carry8ColumnSize13 := by
  dsimp only [carry8ColumnBlocks13, carry8ColumnSize13]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent14 :
    (carry8ColumnBlocks14.toList.map Block.length).sum = carry8ColumnSize14 := by
  dsimp only [carry8ColumnBlocks14, carry8ColumnSize14]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent15 :
    (carry8ColumnBlocks15.toList.map Block.length).sum = carry8ColumnSize15 := by
  dsimp only [carry8ColumnBlocks15, carry8ColumnSize15]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent16 :
    (carry8ColumnBlocks16.toList.map Block.length).sum = carry8ColumnSize16 := by
  dsimp only [carry8ColumnBlocks16, carry8ColumnSize16]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent17 :
    (carry8ColumnBlocks17.toList.map Block.length).sum = carry8ColumnSize17 := by
  dsimp only [carry8ColumnBlocks17, carry8ColumnSize17]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent18 :
    (carry8ColumnBlocks18.toList.map Block.length).sum = carry8ColumnSize18 := by
  dsimp only [carry8ColumnBlocks18, carry8ColumnSize18]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent19 :
    (carry8ColumnBlocks19.toList.map Block.length).sum = carry8ColumnSize19 := by
  dsimp only [carry8ColumnBlocks19, carry8ColumnSize19]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent20 :
    (carry8ColumnBlocks20.toList.map Block.length).sum = carry8ColumnSize20 := by
  dsimp only [carry8ColumnBlocks20, carry8ColumnSize20]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent21 :
    (carry8ColumnBlocks21.toList.map Block.length).sum = carry8ColumnSize21 := by
  dsimp only [carry8ColumnBlocks21, carry8ColumnSize21]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent22 :
    (carry8ColumnBlocks22.toList.map Block.length).sum = carry8ColumnSize22 := by
  dsimp only [carry8ColumnBlocks22, carry8ColumnSize22]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent23 :
    (carry8ColumnBlocks23.toList.map Block.length).sum = carry8ColumnSize23 := by
  dsimp only [carry8ColumnBlocks23, carry8ColumnSize23]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent24 :
    (carry8ColumnBlocks24.toList.map Block.length).sum = carry8ColumnSize24 := by
  dsimp only [carry8ColumnBlocks24, carry8ColumnSize24]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent25 :
    (carry8ColumnBlocks25.toList.map Block.length).sum = carry8ColumnSize25 := by
  dsimp only [carry8ColumnBlocks25, carry8ColumnSize25]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent26 :
    (carry8ColumnBlocks26.toList.map Block.length).sum = carry8ColumnSize26 := by
  dsimp only [carry8ColumnBlocks26, carry8ColumnSize26]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent27 :
    (carry8ColumnBlocks27.toList.map Block.length).sum = carry8ColumnSize27 := by
  dsimp only [carry8ColumnBlocks27, carry8ColumnSize27]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent28 :
    (carry8ColumnBlocks28.toList.map Block.length).sum = carry8ColumnSize28 := by
  dsimp only [carry8ColumnBlocks28, carry8ColumnSize28]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent29 :
    (carry8ColumnBlocks29.toList.map Block.length).sum = carry8ColumnSize29 := by
  dsimp only [carry8ColumnBlocks29, carry8ColumnSize29]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent30 :
    (carry8ColumnBlocks30.toList.map Block.length).sum = carry8ColumnSize30 := by
  dsimp only [carry8ColumnBlocks30, carry8ColumnSize30]
  simp (config := { maxSteps := 1000000 }) [Block.length]


theorem extent31 :
    (carry8ColumnBlocks31.toList.map Block.length).sum = carry8ColumnSize31 := by
  dsimp only [carry8ColumnBlocks31, carry8ColumnSize31]
  simp (config := { maxSteps := 1000000 }) [Block.length]


end Airbender.Blake2Round.Proofs.Carry8Certificate
