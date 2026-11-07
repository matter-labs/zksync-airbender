import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group396 : List Block := [dataT29Column2Block1609,dataT29Column2Block1610,dataT29Column2Block1611,dataT29Column2Block1612,dataT29Column2Block1613,dataT29Column2Block1614,dataT29Column2Block1615,dataT29Column2Block1616]

theorem length396 : (group396.map Block.length).sum = 64 := by
  simp [group396,dataT29Column2Block1609,dataT29Column2Block1610,dataT29Column2Block1611,dataT29Column2Block1612,dataT29Column2Block1613,dataT29Column2Block1614,dataT29Column2Block1615,dataT29Column2Block1616,Block.length]

theorem checked396 : checkBlocks (fun n => n/512 ^^^ n%512) 175672 group396 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group397 : List Block := [dataT29Column2Block1617,dataT29Column2Block1618,dataT29Column2Block1619,dataT29Column2Block1620,dataT29Column2Block1621,dataT29Column2Block1622,dataT29Column2Block1623,dataT29Column2Block1624]

theorem length397 : (group397.map Block.length).sum = 64 := by
  simp [group397,dataT29Column2Block1617,dataT29Column2Block1618,dataT29Column2Block1619,dataT29Column2Block1620,dataT29Column2Block1621,dataT29Column2Block1622,dataT29Column2Block1623,dataT29Column2Block1624,Block.length]

theorem checked397 : checkBlocks (fun n => n/512 ^^^ n%512) 175736 group397 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group398 : List Block := [dataT29Column2Block1625,dataT29Column2Block1626,dataT29Column2Block1627,dataT29Column2Block1628,dataT29Column2Block1629,dataT29Column2Block1630,dataT29Column2Block1631,dataT29Column2Block1632]

theorem length398 : (group398.map Block.length).sum = 64 := by
  simp [group398,dataT29Column2Block1625,dataT29Column2Block1626,dataT29Column2Block1627,dataT29Column2Block1628,dataT29Column2Block1629,dataT29Column2Block1630,dataT29Column2Block1631,dataT29Column2Block1632,Block.length]

theorem checked398 : checkBlocks (fun n => n/512 ^^^ n%512) 175800 group398 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group399 : List Block := [dataT29Column2Block1633,dataT29Column2Block1634,dataT29Column2Block1635,dataT29Column2Block1636,dataT29Column2Block1637,dataT29Column2Block1638,dataT29Column2Block1639,dataT29Column2Block1640]

theorem length399 : (group399.map Block.length).sum = 64 := by
  simp [group399,dataT29Column2Block1633,dataT29Column2Block1634,dataT29Column2Block1635,dataT29Column2Block1636,dataT29Column2Block1637,dataT29Column2Block1638,dataT29Column2Block1639,dataT29Column2Block1640,Block.length]

theorem checked399 : checkBlocks (fun n => n/512 ^^^ n%512) 175864 group399 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
