import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group400 : List Block := [dataT29Column2Block1641,dataT29Column2Block1642,dataT29Column2Block1643,dataT29Column2Block1644,dataT29Column2Block1645,dataT29Column2Block1646,dataT29Column2Block1647,dataT29Column2Block1648]

theorem length400 : (group400.map Block.length).sum = 64 := by
  simp [group400,dataT29Column2Block1641,dataT29Column2Block1642,dataT29Column2Block1643,dataT29Column2Block1644,dataT29Column2Block1645,dataT29Column2Block1646,dataT29Column2Block1647,dataT29Column2Block1648,Block.length]

theorem checked400 : checkBlocks (fun n => n/512 ^^^ n%512) 175928 group400 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group401 : List Block := [dataT29Column2Block1649,dataT29Column2Block1650,dataT29Column2Block1651,dataT29Column2Block1652,dataT29Column2Block1653,dataT29Column2Block1654,dataT29Column2Block1655,dataT29Column2Block1656]

theorem length401 : (group401.map Block.length).sum = 64 := by
  simp [group401,dataT29Column2Block1649,dataT29Column2Block1650,dataT29Column2Block1651,dataT29Column2Block1652,dataT29Column2Block1653,dataT29Column2Block1654,dataT29Column2Block1655,dataT29Column2Block1656,Block.length]

theorem checked401 : checkBlocks (fun n => n/512 ^^^ n%512) 175992 group401 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group402 : List Block := [dataT29Column2Block1657,dataT29Column2Block1658,dataT29Column2Block1659,dataT29Column2Block1660,dataT29Column2Block1661,dataT29Column2Block1662,dataT29Column2Block1663,dataT29Column2Block1664]

theorem length402 : (group402.map Block.length).sum = 64 := by
  simp [group402,dataT29Column2Block1657,dataT29Column2Block1658,dataT29Column2Block1659,dataT29Column2Block1660,dataT29Column2Block1661,dataT29Column2Block1662,dataT29Column2Block1663,dataT29Column2Block1664,Block.length]

theorem checked402 : checkBlocks (fun n => n/512 ^^^ n%512) 176056 group402 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group403 : List Block := [dataT29Column2Block1665,dataT29Column2Block1666,dataT29Column2Block1667,dataT29Column2Block1668,dataT29Column2Block1669,dataT29Column2Block1670,dataT29Column2Block1671,dataT29Column2Block1672]

theorem length403 : (group403.map Block.length).sum = 232 := by
  simp [group403,dataT29Column2Block1665,dataT29Column2Block1666,dataT29Column2Block1667,dataT29Column2Block1668,dataT29Column2Block1669,dataT29Column2Block1670,dataT29Column2Block1671,dataT29Column2Block1672,Block.length]

theorem checked403 : checkBlocks (fun n => n/512 ^^^ n%512) 176120 group403 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
