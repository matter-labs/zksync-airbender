import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group388 : List Block := [dataT29Column2Block1546,dataT29Column2Block1547,dataT29Column2Block1548,dataT29Column2Block1549,dataT29Column2Block1550,dataT29Column2Block1551,dataT29Column2Block1552,dataT29Column2Block1553]

theorem length388 : (group388.map Block.length).sum = 64 := by
  simp [group388,dataT29Column2Block1546,dataT29Column2Block1547,dataT29Column2Block1548,dataT29Column2Block1549,dataT29Column2Block1550,dataT29Column2Block1551,dataT29Column2Block1552,dataT29Column2Block1553,Block.length]

theorem checked388 : checkBlocks (fun n => n/512 ^^^ n%512) 175168 group388 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group389 : List Block := [dataT29Column2Block1554,dataT29Column2Block1555,dataT29Column2Block1556,dataT29Column2Block1557,dataT29Column2Block1558,dataT29Column2Block1559,dataT29Column2Block1560,dataT29Column2Block1561]

theorem length389 : (group389.map Block.length).sum = 64 := by
  simp [group389,dataT29Column2Block1554,dataT29Column2Block1555,dataT29Column2Block1556,dataT29Column2Block1557,dataT29Column2Block1558,dataT29Column2Block1559,dataT29Column2Block1560,dataT29Column2Block1561,Block.length]

theorem checked389 : checkBlocks (fun n => n/512 ^^^ n%512) 175232 group389 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group390 : List Block := [dataT29Column2Block1562,dataT29Column2Block1563,dataT29Column2Block1564,dataT29Column2Block1565,dataT29Column2Block1566,dataT29Column2Block1567,dataT29Column2Block1568,dataT29Column2Block1569]

theorem length390 : (group390.map Block.length).sum = 64 := by
  simp [group390,dataT29Column2Block1562,dataT29Column2Block1563,dataT29Column2Block1564,dataT29Column2Block1565,dataT29Column2Block1566,dataT29Column2Block1567,dataT29Column2Block1568,dataT29Column2Block1569,Block.length]

theorem checked390 : checkBlocks (fun n => n/512 ^^^ n%512) 175296 group390 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group391 : List Block := [dataT29Column2Block1570,dataT29Column2Block1571,dataT29Column2Block1572,dataT29Column2Block1573,dataT29Column2Block1574,dataT29Column2Block1575,dataT29Column2Block1576,dataT29Column2Block1577]

theorem length391 : (group391.map Block.length).sum = 64 := by
  simp [group391,dataT29Column2Block1570,dataT29Column2Block1571,dataT29Column2Block1572,dataT29Column2Block1573,dataT29Column2Block1574,dataT29Column2Block1575,dataT29Column2Block1576,dataT29Column2Block1577,Block.length]

theorem checked391 : checkBlocks (fun n => n/512 ^^^ n%512) 175360 group391 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
