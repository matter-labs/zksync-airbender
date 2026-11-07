import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group372 : List Block := [dataT29Column2Block1425,dataT29Column2Block1426,dataT29Column2Block1427,dataT29Column2Block1428,dataT29Column2Block1429,dataT29Column2Block1430,dataT29Column2Block1431,dataT29Column2Block1432]

theorem length372 : (group372.map Block.length).sum = 32 := by
  simp [group372,dataT29Column2Block1425,dataT29Column2Block1426,dataT29Column2Block1427,dataT29Column2Block1428,dataT29Column2Block1429,dataT29Column2Block1430,dataT29Column2Block1431,dataT29Column2Block1432,Block.length]

theorem checked372 : checkBlocks (fun n => n/512 ^^^ n%512) 174144 group372 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group373 : List Block := [dataT29Column2Block1433,dataT29Column2Block1434,dataT29Column2Block1435,dataT29Column2Block1436,dataT29Column2Block1437,dataT29Column2Block1438,dataT29Column2Block1439,dataT29Column2Block1440]

theorem length373 : (group373.map Block.length).sum = 32 := by
  simp [group373,dataT29Column2Block1433,dataT29Column2Block1434,dataT29Column2Block1435,dataT29Column2Block1436,dataT29Column2Block1437,dataT29Column2Block1438,dataT29Column2Block1439,dataT29Column2Block1440,Block.length]

theorem checked373 : checkBlocks (fun n => n/512 ^^^ n%512) 174176 group373 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group374 : List Block := [dataT29Column2Block1441,dataT29Column2Block1442,dataT29Column2Block1443,dataT29Column2Block1444,dataT29Column2Block1445,dataT29Column2Block1446,dataT29Column2Block1447,dataT29Column2Block1448]

theorem length374 : (group374.map Block.length).sum = 32 := by
  simp [group374,dataT29Column2Block1441,dataT29Column2Block1442,dataT29Column2Block1443,dataT29Column2Block1444,dataT29Column2Block1445,dataT29Column2Block1446,dataT29Column2Block1447,dataT29Column2Block1448,Block.length]

theorem checked374 : checkBlocks (fun n => n/512 ^^^ n%512) 174208 group374 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group375 : List Block := [dataT29Column2Block1449,dataT29Column2Block1450,dataT29Column2Block1451,dataT29Column2Block1452,dataT29Column2Block1453,dataT29Column2Block1454,dataT29Column2Block1455,dataT29Column2Block1456]

theorem length375 : (group375.map Block.length).sum = 32 := by
  simp [group375,dataT29Column2Block1449,dataT29Column2Block1450,dataT29Column2Block1451,dataT29Column2Block1452,dataT29Column2Block1453,dataT29Column2Block1454,dataT29Column2Block1455,dataT29Column2Block1456,Block.length]

theorem checked375 : checkBlocks (fun n => n/512 ^^^ n%512) 174240 group375 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
