import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group404 : List Block := [dataT29Column2Block1673,dataT29Column2Block1674,dataT29Column2Block1675,dataT29Column2Block1676,dataT29Column2Block1677,dataT29Column2Block1678,dataT29Column2Block1679,dataT29Column2Block1680]

theorem length404 : (group404.map Block.length).sum = 256 := by
  simp [group404,dataT29Column2Block1673,dataT29Column2Block1674,dataT29Column2Block1675,dataT29Column2Block1676,dataT29Column2Block1677,dataT29Column2Block1678,dataT29Column2Block1679,dataT29Column2Block1680,Block.length]

theorem checked404 : checkBlocks (fun n => n/512 ^^^ n%512) 176352 group404 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group405 : List Block := [dataT29Column2Block1681,dataT29Column2Block1682,dataT29Column2Block1683,dataT29Column2Block1684,dataT29Column2Block1685,dataT29Column2Block1686,dataT29Column2Block1687,dataT29Column2Block1688]

theorem length405 : (group405.map Block.length).sum = 256 := by
  simp [group405,dataT29Column2Block1681,dataT29Column2Block1682,dataT29Column2Block1683,dataT29Column2Block1684,dataT29Column2Block1685,dataT29Column2Block1686,dataT29Column2Block1687,dataT29Column2Block1688,Block.length]

theorem checked405 : checkBlocks (fun n => n/512 ^^^ n%512) 176608 group405 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group406 : List Block := [dataT29Column2Block1689,dataT29Column2Block1690,dataT29Column2Block1691,dataT29Column2Block1692,dataT29Column2Block1693,dataT29Column2Block1694,dataT29Column2Block1695,dataT29Column2Block1696]

theorem length406 : (group406.map Block.length).sum = 256 := by
  simp [group406,dataT29Column2Block1689,dataT29Column2Block1690,dataT29Column2Block1691,dataT29Column2Block1692,dataT29Column2Block1693,dataT29Column2Block1694,dataT29Column2Block1695,dataT29Column2Block1696,Block.length]

theorem checked406 : checkBlocks (fun n => n/512 ^^^ n%512) 176864 group406 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group407 : List Block := [dataT29Column2Block1697,dataT29Column2Block1698,dataT29Column2Block1699,dataT29Column2Block1700,dataT29Column2Block1701,dataT29Column2Block1702,dataT29Column2Block1703,dataT29Column2Block1704]

theorem length407 : (group407.map Block.length).sum = 256 := by
  simp [group407,dataT29Column2Block1697,dataT29Column2Block1698,dataT29Column2Block1699,dataT29Column2Block1700,dataT29Column2Block1701,dataT29Column2Block1702,dataT29Column2Block1703,dataT29Column2Block1704,Block.length]

theorem checked407 : checkBlocks (fun n => n/512 ^^^ n%512) 177120 group407 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
