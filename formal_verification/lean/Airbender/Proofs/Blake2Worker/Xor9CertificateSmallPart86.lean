import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group376 : List Block := [dataT29Column2Block1457,dataT29Column2Block1458,dataT29Column2Block1459,dataT29Column2Block1460,dataT29Column2Block1461,dataT29Column2Block1462,dataT29Column2Block1463,dataT29Column2Block1464]

theorem length376 : (group376.map Block.length).sum = 32 := by
  simp [group376,dataT29Column2Block1457,dataT29Column2Block1458,dataT29Column2Block1459,dataT29Column2Block1460,dataT29Column2Block1461,dataT29Column2Block1462,dataT29Column2Block1463,dataT29Column2Block1464,Block.length]

theorem checked376 : checkBlocks (fun n => n/512 ^^^ n%512) 174272 group376 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group377 : List Block := [dataT29Column2Block1465,dataT29Column2Block1466,dataT29Column2Block1467,dataT29Column2Block1468,dataT29Column2Block1469,dataT29Column2Block1470,dataT29Column2Block1471,dataT29Column2Block1472]

theorem length377 : (group377.map Block.length).sum = 32 := by
  simp [group377,dataT29Column2Block1465,dataT29Column2Block1466,dataT29Column2Block1467,dataT29Column2Block1468,dataT29Column2Block1469,dataT29Column2Block1470,dataT29Column2Block1471,dataT29Column2Block1472,Block.length]

theorem checked377 : checkBlocks (fun n => n/512 ^^^ n%512) 174304 group377 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group378 : List Block := [dataT29Column2Block1473,dataT29Column2Block1474,dataT29Column2Block1475,dataT29Column2Block1476,dataT29Column2Block1477,dataT29Column2Block1478,dataT29Column2Block1479,dataT29Column2Block1480]

theorem length378 : (group378.map Block.length).sum = 32 := by
  simp [group378,dataT29Column2Block1473,dataT29Column2Block1474,dataT29Column2Block1475,dataT29Column2Block1476,dataT29Column2Block1477,dataT29Column2Block1478,dataT29Column2Block1479,dataT29Column2Block1480,Block.length]

theorem checked378 : checkBlocks (fun n => n/512 ^^^ n%512) 174336 group378 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group379 : List Block := [dataT29Column2Block1481,dataT29Column2Block1482,dataT29Column2Block1483,dataT29Column2Block1484,dataT29Column2Block1485,dataT29Column2Block1486,dataT29Column2Block1487,dataT29Column2Block1488]

theorem length379 : (group379.map Block.length).sum = 32 := by
  simp [group379,dataT29Column2Block1481,dataT29Column2Block1482,dataT29Column2Block1483,dataT29Column2Block1484,dataT29Column2Block1485,dataT29Column2Block1486,dataT29Column2Block1487,dataT29Column2Block1488,Block.length]

theorem checked379 : checkBlocks (fun n => n/512 ^^^ n%512) 174368 group379 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
