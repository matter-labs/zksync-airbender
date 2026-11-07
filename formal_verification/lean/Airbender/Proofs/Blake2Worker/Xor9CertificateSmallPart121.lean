import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group516 : List Block := [dataT29Column2Block1986]

theorem length516 : (group516.map Block.length).sum = 512 := by
  simp [group516,dataT29Column2Block1986,Block.length]

theorem checked516 : checkBlocks (fun n => n/512 ^^^ n%512) 229376 group516 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group517 : List Block := [dataT29Column2Block1987]

theorem length517 : (group517.map Block.length).sum = 512 := by
  simp [group517,dataT29Column2Block1987,Block.length]

theorem checked517 : checkBlocks (fun n => n/512 ^^^ n%512) 229888 group517 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group518 : List Block := [dataT29Column2Block1988]

theorem length518 : (group518.map Block.length).sum = 512 := by
  simp [group518,dataT29Column2Block1988,Block.length]

theorem checked518 : checkBlocks (fun n => n/512 ^^^ n%512) 230400 group518 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group519 : List Block := [dataT29Column2Block1989]

theorem length519 : (group519.map Block.length).sum = 512 := by
  simp [group519,dataT29Column2Block1989,Block.length]

theorem checked519 : checkBlocks (fun n => n/512 ^^^ n%512) 230912 group519 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
