import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group240 : List Block := [dataT29Column2Block958,dataT29Column2Block959]

theorem length240 : (group240.map Block.length).sum = 512 := by
  simp [group240,dataT29Column2Block958,dataT29Column2Block959,Block.length]

theorem checked240 : checkBlocks (fun n => n/512 ^^^ n%512) 113920 group240 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group241 : List Block := [dataT29Column2Block960,dataT29Column2Block961]

theorem length241 : (group241.map Block.length).sum = 512 := by
  simp [group241,dataT29Column2Block960,dataT29Column2Block961,Block.length]

theorem checked241 : checkBlocks (fun n => n/512 ^^^ n%512) 114432 group241 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group242 : List Block := [dataT29Column2Block962,dataT29Column2Block963]

theorem length242 : (group242.map Block.length).sum = 512 := by
  simp [group242,dataT29Column2Block962,dataT29Column2Block963,Block.length]

theorem checked242 : checkBlocks (fun n => n/512 ^^^ n%512) 114944 group242 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group243 : List Block := [dataT29Column2Block964,dataT29Column2Block965]

theorem length243 : (group243.map Block.length).sum = 512 := by
  simp [group243,dataT29Column2Block964,dataT29Column2Block965,Block.length]

theorem checked243 : checkBlocks (fun n => n/512 ^^^ n%512) 115456 group243 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
