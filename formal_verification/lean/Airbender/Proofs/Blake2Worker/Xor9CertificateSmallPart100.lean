import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group432 : List Block := [dataT29Column2Block1845,dataT29Column2Block1846,dataT29Column2Block1847,dataT29Column2Block1848]

theorem length432 : (group432.map Block.length).sum = 512 := by
  simp [group432,dataT29Column2Block1845,dataT29Column2Block1846,dataT29Column2Block1847,dataT29Column2Block1848,Block.length]

theorem checked432 : checkBlocks (fun n => n/512 ^^^ n%512) 186752 group432 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group433 : List Block := [dataT29Column2Block1849,dataT29Column2Block1850,dataT29Column2Block1851,dataT29Column2Block1852]

theorem length433 : (group433.map Block.length).sum = 512 := by
  simp [group433,dataT29Column2Block1849,dataT29Column2Block1850,dataT29Column2Block1851,dataT29Column2Block1852,Block.length]

theorem checked433 : checkBlocks (fun n => n/512 ^^^ n%512) 187264 group433 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group434 : List Block := [dataT29Column2Block1853,dataT29Column2Block1854,dataT29Column2Block1855,dataT29Column2Block1856]

theorem length434 : (group434.map Block.length).sum = 512 := by
  simp [group434,dataT29Column2Block1853,dataT29Column2Block1854,dataT29Column2Block1855,dataT29Column2Block1856,Block.length]

theorem checked434 : checkBlocks (fun n => n/512 ^^^ n%512) 187776 group434 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group435 : List Block := [dataT29Column2Block1857,dataT29Column2Block1858,dataT29Column2Block1859,dataT29Column2Block1860]

theorem length435 : (group435.map Block.length).sum = 512 := by
  simp [group435,dataT29Column2Block1857,dataT29Column2Block1858,dataT29Column2Block1859,dataT29Column2Block1860,Block.length]

theorem checked435 : checkBlocks (fun n => n/512 ^^^ n%512) 188288 group435 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
