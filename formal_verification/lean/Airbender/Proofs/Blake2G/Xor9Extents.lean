import Airbender.Proofs.Blake2G.Xor9Partitions

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem extent0 :
    (xor9ColumnBlocks0.toList.map Block.length).sum = xor9ColumnSize0 := by
  dsimp only [xor9ColumnBlocks0, xor9ColumnSize0]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent1 :
    (xor9ColumnBlocks1.toList.map Block.length).sum = xor9ColumnSize1 := by
  dsimp only [xor9ColumnBlocks1, xor9ColumnSize1]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent2 :
    (xor9ColumnBlocks2.toList.map Block.length).sum = xor9ColumnSize2 := by
  dsimp only [xor9ColumnBlocks2, xor9ColumnSize2]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent3 :
    (xor9ColumnBlocks3.toList.map Block.length).sum = xor9ColumnSize3 := by
  dsimp only [xor9ColumnBlocks3, xor9ColumnSize3]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent4 :
    (xor9ColumnBlocks4.toList.map Block.length).sum = xor9ColumnSize4 := by
  dsimp only [xor9ColumnBlocks4, xor9ColumnSize4]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent5 :
    (xor9ColumnBlocks5.toList.map Block.length).sum = xor9ColumnSize5 := by
  dsimp only [xor9ColumnBlocks5, xor9ColumnSize5]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent6 :
    (xor9ColumnBlocks6.toList.map Block.length).sum = xor9ColumnSize6 := by
  dsimp only [xor9ColumnBlocks6, xor9ColumnSize6]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent7 :
    (xor9ColumnBlocks7.toList.map Block.length).sum = xor9ColumnSize7 := by
  dsimp only [xor9ColumnBlocks7, xor9ColumnSize7]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent8 :
    (xor9ColumnBlocks8.toList.map Block.length).sum = xor9ColumnSize8 := by
  dsimp only [xor9ColumnBlocks8, xor9ColumnSize8]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent9 :
    (xor9ColumnBlocks9.toList.map Block.length).sum = xor9ColumnSize9 := by
  dsimp only [xor9ColumnBlocks9, xor9ColumnSize9]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent10 :
    (xor9ColumnBlocks10.toList.map Block.length).sum = xor9ColumnSize10 := by
  dsimp only [xor9ColumnBlocks10, xor9ColumnSize10]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent11 :
    (xor9ColumnBlocks11.toList.map Block.length).sum = xor9ColumnSize11 := by
  dsimp only [xor9ColumnBlocks11, xor9ColumnSize11]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent12 :
    (xor9ColumnBlocks12.toList.map Block.length).sum = xor9ColumnSize12 := by
  dsimp only [xor9ColumnBlocks12, xor9ColumnSize12]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent13 :
    (xor9ColumnBlocks13.toList.map Block.length).sum = xor9ColumnSize13 := by
  dsimp only [xor9ColumnBlocks13, xor9ColumnSize13]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent14 :
    (xor9ColumnBlocks14.toList.map Block.length).sum = xor9ColumnSize14 := by
  dsimp only [xor9ColumnBlocks14, xor9ColumnSize14]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent15 :
    (xor9ColumnBlocks15.toList.map Block.length).sum = xor9ColumnSize15 := by
  dsimp only [xor9ColumnBlocks15, xor9ColumnSize15]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent16 :
    (xor9ColumnBlocks16.toList.map Block.length).sum = xor9ColumnSize16 := by
  dsimp only [xor9ColumnBlocks16, xor9ColumnSize16]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent17 :
    (xor9ColumnBlocks17.toList.map Block.length).sum = xor9ColumnSize17 := by
  dsimp only [xor9ColumnBlocks17, xor9ColumnSize17]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent18 :
    (xor9ColumnBlocks18.toList.map Block.length).sum = xor9ColumnSize18 := by
  dsimp only [xor9ColumnBlocks18, xor9ColumnSize18]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent19 :
    (xor9ColumnBlocks19.toList.map Block.length).sum = xor9ColumnSize19 := by
  dsimp only [xor9ColumnBlocks19, xor9ColumnSize19]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent20 :
    (xor9ColumnBlocks20.toList.map Block.length).sum = xor9ColumnSize20 := by
  dsimp only [xor9ColumnBlocks20, xor9ColumnSize20]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent21 :
    (xor9ColumnBlocks21.toList.map Block.length).sum = xor9ColumnSize21 := by
  dsimp only [xor9ColumnBlocks21, xor9ColumnSize21]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent22 :
    (xor9ColumnBlocks22.toList.map Block.length).sum = xor9ColumnSize22 := by
  dsimp only [xor9ColumnBlocks22, xor9ColumnSize22]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent23 :
    (xor9ColumnBlocks23.toList.map Block.length).sum = xor9ColumnSize23 := by
  dsimp only [xor9ColumnBlocks23, xor9ColumnSize23]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent24 :
    (xor9ColumnBlocks24.toList.map Block.length).sum = xor9ColumnSize24 := by
  dsimp only [xor9ColumnBlocks24, xor9ColumnSize24]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent25 :
    (xor9ColumnBlocks25.toList.map Block.length).sum = xor9ColumnSize25 := by
  dsimp only [xor9ColumnBlocks25, xor9ColumnSize25]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent26 :
    (xor9ColumnBlocks26.toList.map Block.length).sum = xor9ColumnSize26 := by
  dsimp only [xor9ColumnBlocks26, xor9ColumnSize26]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent27 :
    (xor9ColumnBlocks27.toList.map Block.length).sum = xor9ColumnSize27 := by
  dsimp only [xor9ColumnBlocks27, xor9ColumnSize27]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent28 :
    (xor9ColumnBlocks28.toList.map Block.length).sum = xor9ColumnSize28 := by
  dsimp only [xor9ColumnBlocks28, xor9ColumnSize28]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent29 :
    (xor9ColumnBlocks29.toList.map Block.length).sum = xor9ColumnSize29 := by
  dsimp only [xor9ColumnBlocks29, xor9ColumnSize29]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent30 :
    (xor9ColumnBlocks30.toList.map Block.length).sum = xor9ColumnSize30 := by
  dsimp only [xor9ColumnBlocks30, xor9ColumnSize30]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent31 :
    (xor9ColumnBlocks31.toList.map Block.length).sum = xor9ColumnSize31 := by
  dsimp only [xor9ColumnBlocks31, xor9ColumnSize31]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent32 :
    (xor9ColumnBlocks32.toList.map Block.length).sum = xor9ColumnSize32 := by
  dsimp only [xor9ColumnBlocks32, xor9ColumnSize32]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent33 :
    (xor9ColumnBlocks33.toList.map Block.length).sum = xor9ColumnSize33 := by
  dsimp only [xor9ColumnBlocks33, xor9ColumnSize33]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent34 :
    (xor9ColumnBlocks34.toList.map Block.length).sum = xor9ColumnSize34 := by
  dsimp only [xor9ColumnBlocks34, xor9ColumnSize34]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent35 :
    (xor9ColumnBlocks35.toList.map Block.length).sum = xor9ColumnSize35 := by
  dsimp only [xor9ColumnBlocks35, xor9ColumnSize35]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent36 :
    (xor9ColumnBlocks36.toList.map Block.length).sum = xor9ColumnSize36 := by
  dsimp only [xor9ColumnBlocks36, xor9ColumnSize36]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent37 :
    (xor9ColumnBlocks37.toList.map Block.length).sum = xor9ColumnSize37 := by
  dsimp only [xor9ColumnBlocks37, xor9ColumnSize37]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent38 :
    (xor9ColumnBlocks38.toList.map Block.length).sum = xor9ColumnSize38 := by
  dsimp only [xor9ColumnBlocks38, xor9ColumnSize38]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent39 :
    (xor9ColumnBlocks39.toList.map Block.length).sum = xor9ColumnSize39 := by
  dsimp only [xor9ColumnBlocks39, xor9ColumnSize39]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent40 :
    (xor9ColumnBlocks40.toList.map Block.length).sum = xor9ColumnSize40 := by
  dsimp only [xor9ColumnBlocks40, xor9ColumnSize40]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent41 :
    (xor9ColumnBlocks41.toList.map Block.length).sum = xor9ColumnSize41 := by
  dsimp only [xor9ColumnBlocks41, xor9ColumnSize41]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent42 :
    (xor9ColumnBlocks42.toList.map Block.length).sum = xor9ColumnSize42 := by
  dsimp only [xor9ColumnBlocks42, xor9ColumnSize42]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent43 :
    (xor9ColumnBlocks43.toList.map Block.length).sum = xor9ColumnSize43 := by
  dsimp only [xor9ColumnBlocks43, xor9ColumnSize43]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent44 :
    (xor9ColumnBlocks44.toList.map Block.length).sum = xor9ColumnSize44 := by
  dsimp only [xor9ColumnBlocks44, xor9ColumnSize44]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent45 :
    (xor9ColumnBlocks45.toList.map Block.length).sum = xor9ColumnSize45 := by
  dsimp only [xor9ColumnBlocks45, xor9ColumnSize45]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent46 :
    (xor9ColumnBlocks46.toList.map Block.length).sum = xor9ColumnSize46 := by
  dsimp only [xor9ColumnBlocks46, xor9ColumnSize46]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent47 :
    (xor9ColumnBlocks47.toList.map Block.length).sum = xor9ColumnSize47 := by
  dsimp only [xor9ColumnBlocks47, xor9ColumnSize47]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent48 :
    (xor9ColumnBlocks48.toList.map Block.length).sum = xor9ColumnSize48 := by
  dsimp only [xor9ColumnBlocks48, xor9ColumnSize48]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent49 :
    (xor9ColumnBlocks49.toList.map Block.length).sum = xor9ColumnSize49 := by
  dsimp only [xor9ColumnBlocks49, xor9ColumnSize49]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent50 :
    (xor9ColumnBlocks50.toList.map Block.length).sum = xor9ColumnSize50 := by
  dsimp only [xor9ColumnBlocks50, xor9ColumnSize50]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent51 :
    (xor9ColumnBlocks51.toList.map Block.length).sum = xor9ColumnSize51 := by
  dsimp only [xor9ColumnBlocks51, xor9ColumnSize51]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent52 :
    (xor9ColumnBlocks52.toList.map Block.length).sum = xor9ColumnSize52 := by
  dsimp only [xor9ColumnBlocks52, xor9ColumnSize52]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent53 :
    (xor9ColumnBlocks53.toList.map Block.length).sum = xor9ColumnSize53 := by
  dsimp only [xor9ColumnBlocks53, xor9ColumnSize53]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent54 :
    (xor9ColumnBlocks54.toList.map Block.length).sum = xor9ColumnSize54 := by
  dsimp only [xor9ColumnBlocks54, xor9ColumnSize54]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent55 :
    (xor9ColumnBlocks55.toList.map Block.length).sum = xor9ColumnSize55 := by
  dsimp only [xor9ColumnBlocks55, xor9ColumnSize55]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent56 :
    (xor9ColumnBlocks56.toList.map Block.length).sum = xor9ColumnSize56 := by
  dsimp only [xor9ColumnBlocks56, xor9ColumnSize56]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent57 :
    (xor9ColumnBlocks57.toList.map Block.length).sum = xor9ColumnSize57 := by
  dsimp only [xor9ColumnBlocks57, xor9ColumnSize57]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent58 :
    (xor9ColumnBlocks58.toList.map Block.length).sum = xor9ColumnSize58 := by
  dsimp only [xor9ColumnBlocks58, xor9ColumnSize58]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent59 :
    (xor9ColumnBlocks59.toList.map Block.length).sum = xor9ColumnSize59 := by
  dsimp only [xor9ColumnBlocks59, xor9ColumnSize59]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent60 :
    (xor9ColumnBlocks60.toList.map Block.length).sum = xor9ColumnSize60 := by
  dsimp only [xor9ColumnBlocks60, xor9ColumnSize60]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent61 :
    (xor9ColumnBlocks61.toList.map Block.length).sum = xor9ColumnSize61 := by
  dsimp only [xor9ColumnBlocks61, xor9ColumnSize61]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent62 :
    (xor9ColumnBlocks62.toList.map Block.length).sum = xor9ColumnSize62 := by
  dsimp only [xor9ColumnBlocks62, xor9ColumnSize62]
  simp (config := { maxSteps := 1000000 }) [Block.length]

theorem extent63 :
    (xor9ColumnBlocks63.toList.map Block.length).sum = xor9ColumnSize63 := by
  dsimp only [xor9ColumnBlocks63, xor9ColumnSize63]
  simp (config := { maxSteps := 1000000 }) [Block.length]

end Airbender.Blake2G.Proofs.Xor9Certificate
