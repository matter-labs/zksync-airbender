import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group416 : List Block := [dataT29Column2Block1769,dataT29Column2Block1770,dataT29Column2Block1771,dataT29Column2Block1772,dataT29Column2Block1773,dataT29Column2Block1774,dataT29Column2Block1775,dataT29Column2Block1776]

theorem length416 : (group416.map Block.length).sum = 256 := by
  simp [group416,dataT29Column2Block1769,dataT29Column2Block1770,dataT29Column2Block1771,dataT29Column2Block1772,dataT29Column2Block1773,dataT29Column2Block1774,dataT29Column2Block1775,dataT29Column2Block1776,Block.length]

theorem checked416 : checkBlocks (fun n => n/512 ^^^ n%512) 179424 group416 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group417 : List Block := [dataT29Column2Block1777,dataT29Column2Block1778,dataT29Column2Block1779,dataT29Column2Block1780,dataT29Column2Block1781,dataT29Column2Block1782,dataT29Column2Block1783,dataT29Column2Block1784]

theorem length417 : (group417.map Block.length).sum = 256 := by
  simp [group417,dataT29Column2Block1777,dataT29Column2Block1778,dataT29Column2Block1779,dataT29Column2Block1780,dataT29Column2Block1781,dataT29Column2Block1782,dataT29Column2Block1783,dataT29Column2Block1784,Block.length]

theorem checked417 : checkBlocks (fun n => n/512 ^^^ n%512) 179680 group417 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group418 : List Block := [dataT29Column2Block1785,dataT29Column2Block1786,dataT29Column2Block1787,dataT29Column2Block1788,dataT29Column2Block1789,dataT29Column2Block1790,dataT29Column2Block1791,dataT29Column2Block1792]

theorem length418 : (group418.map Block.length).sum = 256 := by
  simp [group418,dataT29Column2Block1785,dataT29Column2Block1786,dataT29Column2Block1787,dataT29Column2Block1788,dataT29Column2Block1789,dataT29Column2Block1790,dataT29Column2Block1791,dataT29Column2Block1792,Block.length]

theorem checked418 : checkBlocks (fun n => n/512 ^^^ n%512) 179936 group418 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group419 : List Block := [dataT29Column2Block1793,dataT29Column2Block1794,dataT29Column2Block1795,dataT29Column2Block1796]

theorem length419 : (group419.map Block.length).sum = 416 := by
  simp [group419,dataT29Column2Block1793,dataT29Column2Block1794,dataT29Column2Block1795,dataT29Column2Block1796,Block.length]

theorem checked419 : checkBlocks (fun n => n/512 ^^^ n%512) 180192 group419 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
