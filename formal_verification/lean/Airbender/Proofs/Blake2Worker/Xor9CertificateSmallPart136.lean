import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group576 : List Block := [dataT29Column2Block2046]

theorem length576 : (group576.map Block.length).sum = 512 := by
  simp [group576,dataT29Column2Block2046,Block.length]

theorem checked576 : checkBlocks (fun n => n/512 ^^^ n%512) 260096 group576 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group577 : List Block := [dataT29Column2Block2047]

theorem length577 : (group577.map Block.length).sum = 512 := by
  simp [group577,dataT29Column2Block2047,Block.length]

theorem checked577 : checkBlocks (fun n => n/512 ^^^ n%512) 260608 group577 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group578 : List Block := [dataT29Column2Block2048]

theorem length578 : (group578.map Block.length).sum = 512 := by
  simp [group578,dataT29Column2Block2048,Block.length]

theorem checked578 : checkBlocks (fun n => n/512 ^^^ n%512) 261120 group578 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group579 : List Block := [dataT29Column2Block2049]

theorem length579 : (group579.map Block.length).sum = 512 := by
  simp [group579,dataT29Column2Block2049,Block.length]

theorem checked579 : checkBlocks (fun n => n/512 ^^^ n%512) 261632 group579 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
