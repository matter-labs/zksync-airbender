import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group408 : List Block := [dataT29Column2Block1705,dataT29Column2Block1706,dataT29Column2Block1707,dataT29Column2Block1708,dataT29Column2Block1709,dataT29Column2Block1710,dataT29Column2Block1711,dataT29Column2Block1712]

theorem length408 : (group408.map Block.length).sum = 256 := by
  simp [group408,dataT29Column2Block1705,dataT29Column2Block1706,dataT29Column2Block1707,dataT29Column2Block1708,dataT29Column2Block1709,dataT29Column2Block1710,dataT29Column2Block1711,dataT29Column2Block1712,Block.length]

theorem checked408 : checkBlocks (fun n => n/512 ^^^ n%512) 177376 group408 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group409 : List Block := [dataT29Column2Block1713,dataT29Column2Block1714,dataT29Column2Block1715,dataT29Column2Block1716,dataT29Column2Block1717,dataT29Column2Block1718,dataT29Column2Block1719,dataT29Column2Block1720]

theorem length409 : (group409.map Block.length).sum = 256 := by
  simp [group409,dataT29Column2Block1713,dataT29Column2Block1714,dataT29Column2Block1715,dataT29Column2Block1716,dataT29Column2Block1717,dataT29Column2Block1718,dataT29Column2Block1719,dataT29Column2Block1720,Block.length]

theorem checked409 : checkBlocks (fun n => n/512 ^^^ n%512) 177632 group409 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group410 : List Block := [dataT29Column2Block1721,dataT29Column2Block1722,dataT29Column2Block1723,dataT29Column2Block1724,dataT29Column2Block1725,dataT29Column2Block1726,dataT29Column2Block1727,dataT29Column2Block1728]

theorem length410 : (group410.map Block.length).sum = 256 := by
  simp [group410,dataT29Column2Block1721,dataT29Column2Block1722,dataT29Column2Block1723,dataT29Column2Block1724,dataT29Column2Block1725,dataT29Column2Block1726,dataT29Column2Block1727,dataT29Column2Block1728,Block.length]

theorem checked410 : checkBlocks (fun n => n/512 ^^^ n%512) 177888 group410 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group411 : List Block := [dataT29Column2Block1729,dataT29Column2Block1730,dataT29Column2Block1731,dataT29Column2Block1732,dataT29Column2Block1733,dataT29Column2Block1734,dataT29Column2Block1735,dataT29Column2Block1736]

theorem length411 : (group411.map Block.length).sum = 256 := by
  simp [group411,dataT29Column2Block1729,dataT29Column2Block1730,dataT29Column2Block1731,dataT29Column2Block1732,dataT29Column2Block1733,dataT29Column2Block1734,dataT29Column2Block1735,dataT29Column2Block1736,Block.length]

theorem checked411 : checkBlocks (fun n => n/512 ^^^ n%512) 178144 group411 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
