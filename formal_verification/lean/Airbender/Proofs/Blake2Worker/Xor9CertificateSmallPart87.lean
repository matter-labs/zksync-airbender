import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group380 : List Block := [dataT29Column2Block1489,dataT29Column2Block1490,dataT29Column2Block1491,dataT29Column2Block1492,dataT29Column2Block1493,dataT29Column2Block1494,dataT29Column2Block1495,dataT29Column2Block1496]

theorem length380 : (group380.map Block.length).sum = 32 := by
  simp [group380,dataT29Column2Block1489,dataT29Column2Block1490,dataT29Column2Block1491,dataT29Column2Block1492,dataT29Column2Block1493,dataT29Column2Block1494,dataT29Column2Block1495,dataT29Column2Block1496,Block.length]

theorem checked380 : checkBlocks (fun n => n/512 ^^^ n%512) 174400 group380 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group381 : List Block := [dataT29Column2Block1497,dataT29Column2Block1498,dataT29Column2Block1499,dataT29Column2Block1500,dataT29Column2Block1501,dataT29Column2Block1502,dataT29Column2Block1503,dataT29Column2Block1504]

theorem length381 : (group381.map Block.length).sum = 32 := by
  simp [group381,dataT29Column2Block1497,dataT29Column2Block1498,dataT29Column2Block1499,dataT29Column2Block1500,dataT29Column2Block1501,dataT29Column2Block1502,dataT29Column2Block1503,dataT29Column2Block1504,Block.length]

theorem checked381 : checkBlocks (fun n => n/512 ^^^ n%512) 174432 group381 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group382 : List Block := [dataT29Column2Block1505,dataT29Column2Block1506,dataT29Column2Block1507,dataT29Column2Block1508,dataT29Column2Block1509,dataT29Column2Block1510,dataT29Column2Block1511,dataT29Column2Block1512]

theorem length382 : (group382.map Block.length).sum = 32 := by
  simp [group382,dataT29Column2Block1505,dataT29Column2Block1506,dataT29Column2Block1507,dataT29Column2Block1508,dataT29Column2Block1509,dataT29Column2Block1510,dataT29Column2Block1511,dataT29Column2Block1512,Block.length]

theorem checked382 : checkBlocks (fun n => n/512 ^^^ n%512) 174464 group382 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group383 : List Block := [dataT29Column2Block1513,dataT29Column2Block1514,dataT29Column2Block1515,dataT29Column2Block1516,dataT29Column2Block1517,dataT29Column2Block1518,dataT29Column2Block1519,dataT29Column2Block1520]

theorem length383 : (group383.map Block.length).sum = 32 := by
  simp [group383,dataT29Column2Block1513,dataT29Column2Block1514,dataT29Column2Block1515,dataT29Column2Block1516,dataT29Column2Block1517,dataT29Column2Block1518,dataT29Column2Block1519,dataT29Column2Block1520,Block.length]

theorem checked383 : checkBlocks (fun n => n/512 ^^^ n%512) 174496 group383 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
