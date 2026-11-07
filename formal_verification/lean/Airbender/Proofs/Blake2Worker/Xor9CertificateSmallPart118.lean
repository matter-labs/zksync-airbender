import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group504 : List Block := [dataT29Column2Block1974]

theorem length504 : (group504.map Block.length).sum = 512 := by
  simp [group504,dataT29Column2Block1974,Block.length]

theorem checked504 : checkBlocks (fun n => n/512 ^^^ n%512) 223232 group504 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group505 : List Block := [dataT29Column2Block1975]

theorem length505 : (group505.map Block.length).sum = 512 := by
  simp [group505,dataT29Column2Block1975,Block.length]

theorem checked505 : checkBlocks (fun n => n/512 ^^^ n%512) 223744 group505 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group506 : List Block := [dataT29Column2Block1976]

theorem length506 : (group506.map Block.length).sum = 512 := by
  simp [group506,dataT29Column2Block1976,Block.length]

theorem checked506 : checkBlocks (fun n => n/512 ^^^ n%512) 224256 group506 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group507 : List Block := [dataT29Column2Block1977]

theorem length507 : (group507.map Block.length).sum = 512 := by
  simp [group507,dataT29Column2Block1977,Block.length]

theorem checked507 : checkBlocks (fun n => n/512 ^^^ n%512) 224768 group507 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
