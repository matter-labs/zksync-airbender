import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group392 : List Block := [dataT29Column2Block1578,dataT29Column2Block1579,dataT29Column2Block1580,dataT29Column2Block1581,dataT29Column2Block1582,dataT29Column2Block1583,dataT29Column2Block1584,dataT29Column2Block1585]

theorem length392 : (group392.map Block.length).sum = 64 := by
  simp [group392,dataT29Column2Block1578,dataT29Column2Block1579,dataT29Column2Block1580,dataT29Column2Block1581,dataT29Column2Block1582,dataT29Column2Block1583,dataT29Column2Block1584,dataT29Column2Block1585,Block.length]

theorem checked392 : checkBlocks (fun n => n/512 ^^^ n%512) 175424 group392 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group393 : List Block := [dataT29Column2Block1586,dataT29Column2Block1587,dataT29Column2Block1588,dataT29Column2Block1589,dataT29Column2Block1590,dataT29Column2Block1591,dataT29Column2Block1592,dataT29Column2Block1593]

theorem length393 : (group393.map Block.length).sum = 64 := by
  simp [group393,dataT29Column2Block1586,dataT29Column2Block1587,dataT29Column2Block1588,dataT29Column2Block1589,dataT29Column2Block1590,dataT29Column2Block1591,dataT29Column2Block1592,dataT29Column2Block1593,Block.length]

theorem checked393 : checkBlocks (fun n => n/512 ^^^ n%512) 175488 group393 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group394 : List Block := [dataT29Column2Block1594,dataT29Column2Block1595,dataT29Column2Block1596,dataT29Column2Block1597,dataT29Column2Block1598,dataT29Column2Block1599,dataT29Column2Block1600]

theorem length394 : (group394.map Block.length).sum = 56 := by
  simp [group394,dataT29Column2Block1594,dataT29Column2Block1595,dataT29Column2Block1596,dataT29Column2Block1597,dataT29Column2Block1598,dataT29Column2Block1599,dataT29Column2Block1600,Block.length]

theorem checked394 : checkBlocks (fun n => n/512 ^^^ n%512) 175552 group394 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group395 : List Block := [dataT29Column2Block1601,dataT29Column2Block1602,dataT29Column2Block1603,dataT29Column2Block1604,dataT29Column2Block1605,dataT29Column2Block1606,dataT29Column2Block1607,dataT29Column2Block1608]

theorem length395 : (group395.map Block.length).sum = 64 := by
  simp [group395,dataT29Column2Block1601,dataT29Column2Block1602,dataT29Column2Block1603,dataT29Column2Block1604,dataT29Column2Block1605,dataT29Column2Block1606,dataT29Column2Block1607,dataT29Column2Block1608,Block.length]

theorem checked395 : checkBlocks (fun n => n/512 ^^^ n%512) 175608 group395 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
