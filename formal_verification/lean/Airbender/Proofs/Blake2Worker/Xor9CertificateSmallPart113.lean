import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group484 : List Block := [dataT29Column2Block1954]

theorem length484 : (group484.map Block.length).sum = 512 := by
  simp [group484,dataT29Column2Block1954,Block.length]

theorem checked484 : checkBlocks (fun n => n/512 ^^^ n%512) 212992 group484 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group485 : List Block := [dataT29Column2Block1955]

theorem length485 : (group485.map Block.length).sum = 512 := by
  simp [group485,dataT29Column2Block1955,Block.length]

theorem checked485 : checkBlocks (fun n => n/512 ^^^ n%512) 213504 group485 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group486 : List Block := [dataT29Column2Block1956]

theorem length486 : (group486.map Block.length).sum = 512 := by
  simp [group486,dataT29Column2Block1956,Block.length]

theorem checked486 : checkBlocks (fun n => n/512 ^^^ n%512) 214016 group486 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group487 : List Block := [dataT29Column2Block1957]

theorem length487 : (group487.map Block.length).sum = 512 := by
  simp [group487,dataT29Column2Block1957,Block.length]

theorem checked487 : checkBlocks (fun n => n/512 ^^^ n%512) 214528 group487 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
