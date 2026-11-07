import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group412 : List Block := [dataT29Column2Block1737,dataT29Column2Block1738,dataT29Column2Block1739,dataT29Column2Block1740,dataT29Column2Block1741,dataT29Column2Block1742,dataT29Column2Block1743,dataT29Column2Block1744]

theorem length412 : (group412.map Block.length).sum = 256 := by
  simp [group412,dataT29Column2Block1737,dataT29Column2Block1738,dataT29Column2Block1739,dataT29Column2Block1740,dataT29Column2Block1741,dataT29Column2Block1742,dataT29Column2Block1743,dataT29Column2Block1744,Block.length]

theorem checked412 : checkBlocks (fun n => n/512 ^^^ n%512) 178400 group412 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group413 : List Block := [dataT29Column2Block1745,dataT29Column2Block1746,dataT29Column2Block1747,dataT29Column2Block1748,dataT29Column2Block1749,dataT29Column2Block1750,dataT29Column2Block1751,dataT29Column2Block1752]

theorem length413 : (group413.map Block.length).sum = 256 := by
  simp [group413,dataT29Column2Block1745,dataT29Column2Block1746,dataT29Column2Block1747,dataT29Column2Block1748,dataT29Column2Block1749,dataT29Column2Block1750,dataT29Column2Block1751,dataT29Column2Block1752,Block.length]

theorem checked413 : checkBlocks (fun n => n/512 ^^^ n%512) 178656 group413 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group414 : List Block := [dataT29Column2Block1753,dataT29Column2Block1754,dataT29Column2Block1755,dataT29Column2Block1756,dataT29Column2Block1757,dataT29Column2Block1758,dataT29Column2Block1759,dataT29Column2Block1760]

theorem length414 : (group414.map Block.length).sum = 256 := by
  simp [group414,dataT29Column2Block1753,dataT29Column2Block1754,dataT29Column2Block1755,dataT29Column2Block1756,dataT29Column2Block1757,dataT29Column2Block1758,dataT29Column2Block1759,dataT29Column2Block1760,Block.length]

theorem checked414 : checkBlocks (fun n => n/512 ^^^ n%512) 178912 group414 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group415 : List Block := [dataT29Column2Block1761,dataT29Column2Block1762,dataT29Column2Block1763,dataT29Column2Block1764,dataT29Column2Block1765,dataT29Column2Block1766,dataT29Column2Block1767,dataT29Column2Block1768]

theorem length415 : (group415.map Block.length).sum = 256 := by
  simp [group415,dataT29Column2Block1761,dataT29Column2Block1762,dataT29Column2Block1763,dataT29Column2Block1764,dataT29Column2Block1765,dataT29Column2Block1766,dataT29Column2Block1767,dataT29Column2Block1768,Block.length]

theorem checked415 : checkBlocks (fun n => n/512 ^^^ n%512) 179168 group415 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
