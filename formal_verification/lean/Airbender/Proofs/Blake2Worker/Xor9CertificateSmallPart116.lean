import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group496 : List Block := [dataT29Column2Block1966]

theorem length496 : (group496.map Block.length).sum = 512 := by
  simp [group496,dataT29Column2Block1966,Block.length]

theorem checked496 : checkBlocks (fun n => n/512 ^^^ n%512) 219136 group496 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group497 : List Block := [dataT29Column2Block1967]

theorem length497 : (group497.map Block.length).sum = 512 := by
  simp [group497,dataT29Column2Block1967,Block.length]

theorem checked497 : checkBlocks (fun n => n/512 ^^^ n%512) 219648 group497 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group498 : List Block := [dataT29Column2Block1968]

theorem length498 : (group498.map Block.length).sum = 512 := by
  simp [group498,dataT29Column2Block1968,Block.length]

theorem checked498 : checkBlocks (fun n => n/512 ^^^ n%512) 220160 group498 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group499 : List Block := [dataT29Column2Block1969]

theorem length499 : (group499.map Block.length).sum = 512 := by
  simp [group499,dataT29Column2Block1969,Block.length]

theorem checked499 : checkBlocks (fun n => n/512 ^^^ n%512) 220672 group499 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
