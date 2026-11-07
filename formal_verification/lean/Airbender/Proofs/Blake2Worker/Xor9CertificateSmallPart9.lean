import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group68 : List Block := [dataT29Column2Block100]

theorem length68 : (group68.map Block.length).sum = 512 := by
  simp [group68,dataT29Column2Block100,Block.length]

theorem checked68 : checkBlocks (fun n => n/512 ^^^ n%512) 51200 group68 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group69 : List Block := [dataT29Column2Block101]

theorem length69 : (group69.map Block.length).sum = 512 := by
  simp [group69,dataT29Column2Block101,Block.length]

theorem checked69 : checkBlocks (fun n => n/512 ^^^ n%512) 51712 group69 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group70 : List Block := [dataT29Column2Block102]

theorem length70 : (group70.map Block.length).sum = 512 := by
  simp [group70,dataT29Column2Block102,Block.length]

theorem checked70 : checkBlocks (fun n => n/512 ^^^ n%512) 52224 group70 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group71 : List Block := [dataT29Column2Block103]

theorem length71 : (group71.map Block.length).sum = 512 := by
  simp [group71,dataT29Column2Block103,Block.length]

theorem checked71 : checkBlocks (fun n => n/512 ^^^ n%512) 52736 group71 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
