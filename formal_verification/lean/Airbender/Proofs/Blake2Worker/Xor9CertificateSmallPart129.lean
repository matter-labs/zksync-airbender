import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group548 : List Block := [dataT29Column2Block2018]

theorem length548 : (group548.map Block.length).sum = 512 := by
  simp [group548,dataT29Column2Block2018,Block.length]

theorem checked548 : checkBlocks (fun n => n/512 ^^^ n%512) 245760 group548 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group549 : List Block := [dataT29Column2Block2019]

theorem length549 : (group549.map Block.length).sum = 512 := by
  simp [group549,dataT29Column2Block2019,Block.length]

theorem checked549 : checkBlocks (fun n => n/512 ^^^ n%512) 246272 group549 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group550 : List Block := [dataT29Column2Block2020]

theorem length550 : (group550.map Block.length).sum = 512 := by
  simp [group550,dataT29Column2Block2020,Block.length]

theorem checked550 : checkBlocks (fun n => n/512 ^^^ n%512) 246784 group550 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group551 : List Block := [dataT29Column2Block2021]

theorem length551 : (group551.map Block.length).sum = 512 := by
  simp [group551,dataT29Column2Block2021,Block.length]

theorem checked551 : checkBlocks (fun n => n/512 ^^^ n%512) 247296 group551 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
