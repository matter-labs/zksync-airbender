import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group448 : List Block := [dataT29Column2Block1909,dataT29Column2Block1910,dataT29Column2Block1911,dataT29Column2Block1912]

theorem length448 : (group448.map Block.length).sum = 512 := by
  simp [group448,dataT29Column2Block1909,dataT29Column2Block1910,dataT29Column2Block1911,dataT29Column2Block1912,Block.length]

theorem checked448 : checkBlocks (fun n => n/512 ^^^ n%512) 194944 group448 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group449 : List Block := [dataT29Column2Block1913,dataT29Column2Block1914,dataT29Column2Block1915,dataT29Column2Block1916]

theorem length449 : (group449.map Block.length).sum = 512 := by
  simp [group449,dataT29Column2Block1913,dataT29Column2Block1914,dataT29Column2Block1915,dataT29Column2Block1916,Block.length]

theorem checked449 : checkBlocks (fun n => n/512 ^^^ n%512) 195456 group449 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group450 : List Block := [dataT29Column2Block1917,dataT29Column2Block1918,dataT29Column2Block1919,dataT29Column2Block1920]

theorem length450 : (group450.map Block.length).sum = 512 := by
  simp [group450,dataT29Column2Block1917,dataT29Column2Block1918,dataT29Column2Block1919,dataT29Column2Block1920,Block.length]

theorem checked450 : checkBlocks (fun n => n/512 ^^^ n%512) 195968 group450 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group451 : List Block := [dataT29Column2Block1921]

theorem length451 : (group451.map Block.length).sum = 128 := by
  simp [group451,dataT29Column2Block1921,Block.length]

theorem checked451 : checkBlocks (fun n => n/512 ^^^ n%512) 196480 group451 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
