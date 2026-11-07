import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group568 : List Block := [dataT29Column2Block2038]

theorem length568 : (group568.map Block.length).sum = 512 := by
  simp [group568,dataT29Column2Block2038,Block.length]

theorem checked568 : checkBlocks (fun n => n/512 ^^^ n%512) 256000 group568 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group569 : List Block := [dataT29Column2Block2039]

theorem length569 : (group569.map Block.length).sum = 512 := by
  simp [group569,dataT29Column2Block2039,Block.length]

theorem checked569 : checkBlocks (fun n => n/512 ^^^ n%512) 256512 group569 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group570 : List Block := [dataT29Column2Block2040]

theorem length570 : (group570.map Block.length).sum = 512 := by
  simp [group570,dataT29Column2Block2040,Block.length]

theorem checked570 : checkBlocks (fun n => n/512 ^^^ n%512) 257024 group570 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group571 : List Block := [dataT29Column2Block2041]

theorem length571 : (group571.map Block.length).sum = 512 := by
  simp [group571,dataT29Column2Block2041,Block.length]

theorem checked571 : checkBlocks (fun n => n/512 ^^^ n%512) 257536 group571 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
