import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group452 : List Block := [dataT29Column2Block1922]

theorem length452 : (group452.map Block.length).sum = 512 := by
  simp [group452,dataT29Column2Block1922,Block.length]

theorem checked452 : checkBlocks (fun n => n/512 ^^^ n%512) 196608 group452 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group453 : List Block := [dataT29Column2Block1923]

theorem length453 : (group453.map Block.length).sum = 512 := by
  simp [group453,dataT29Column2Block1923,Block.length]

theorem checked453 : checkBlocks (fun n => n/512 ^^^ n%512) 197120 group453 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group454 : List Block := [dataT29Column2Block1924]

theorem length454 : (group454.map Block.length).sum = 512 := by
  simp [group454,dataT29Column2Block1924,Block.length]

theorem checked454 : checkBlocks (fun n => n/512 ^^^ n%512) 197632 group454 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group455 : List Block := [dataT29Column2Block1925]

theorem length455 : (group455.map Block.length).sum = 512 := by
  simp [group455,dataT29Column2Block1925,Block.length]

theorem checked455 : checkBlocks (fun n => n/512 ^^^ n%512) 198144 group455 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
