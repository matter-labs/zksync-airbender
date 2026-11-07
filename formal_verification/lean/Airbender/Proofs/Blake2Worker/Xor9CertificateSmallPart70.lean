import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group312 : List Block := [dataT29Column2Block1101,dataT29Column2Block1102]

theorem length312 : (group312.map Block.length).sum = 512 := by
  simp [group312,dataT29Column2Block1101,dataT29Column2Block1102,Block.length]

theorem checked312 : checkBlocks (fun n => n/512 ^^^ n%512) 150528 group312 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group313 : List Block := [dataT29Column2Block1103,dataT29Column2Block1104]

theorem length313 : (group313.map Block.length).sum = 512 := by
  simp [group313,dataT29Column2Block1103,dataT29Column2Block1104,Block.length]

theorem checked313 : checkBlocks (fun n => n/512 ^^^ n%512) 151040 group313 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group314 : List Block := [dataT29Column2Block1105,dataT29Column2Block1106]

theorem length314 : (group314.map Block.length).sum = 512 := by
  simp [group314,dataT29Column2Block1105,dataT29Column2Block1106,Block.length]

theorem checked314 : checkBlocks (fun n => n/512 ^^^ n%512) 151552 group314 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group315 : List Block := [dataT29Column2Block1107,dataT29Column2Block1108]

theorem length315 : (group315.map Block.length).sum = 512 := by
  simp [group315,dataT29Column2Block1107,dataT29Column2Block1108,Block.length]

theorem checked315 : checkBlocks (fun n => n/512 ^^^ n%512) 152064 group315 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
