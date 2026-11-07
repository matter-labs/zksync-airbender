import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group440 : List Block := [dataT29Column2Block1877,dataT29Column2Block1878,dataT29Column2Block1879,dataT29Column2Block1880]

theorem length440 : (group440.map Block.length).sum = 512 := by
  simp [group440,dataT29Column2Block1877,dataT29Column2Block1878,dataT29Column2Block1879,dataT29Column2Block1880,Block.length]

theorem checked440 : checkBlocks (fun n => n/512 ^^^ n%512) 190848 group440 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group441 : List Block := [dataT29Column2Block1881,dataT29Column2Block1882,dataT29Column2Block1883,dataT29Column2Block1884]

theorem length441 : (group441.map Block.length).sum = 512 := by
  simp [group441,dataT29Column2Block1881,dataT29Column2Block1882,dataT29Column2Block1883,dataT29Column2Block1884,Block.length]

theorem checked441 : checkBlocks (fun n => n/512 ^^^ n%512) 191360 group441 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group442 : List Block := [dataT29Column2Block1885,dataT29Column2Block1886,dataT29Column2Block1887,dataT29Column2Block1888]

theorem length442 : (group442.map Block.length).sum = 512 := by
  simp [group442,dataT29Column2Block1885,dataT29Column2Block1886,dataT29Column2Block1887,dataT29Column2Block1888,Block.length]

theorem checked442 : checkBlocks (fun n => n/512 ^^^ n%512) 191872 group442 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group443 : List Block := [dataT29Column2Block1889,dataT29Column2Block1890,dataT29Column2Block1891,dataT29Column2Block1892]

theorem length443 : (group443.map Block.length).sum = 512 := by
  simp [group443,dataT29Column2Block1889,dataT29Column2Block1890,dataT29Column2Block1891,dataT29Column2Block1892,Block.length]

theorem checked443 : checkBlocks (fun n => n/512 ^^^ n%512) 192384 group443 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
