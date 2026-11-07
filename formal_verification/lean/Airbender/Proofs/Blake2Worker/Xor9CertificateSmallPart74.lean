import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group328 : List Block := [dataT29Column2Block1133,dataT29Column2Block1134]

theorem length328 : (group328.map Block.length).sum = 512 := by
  simp [group328,dataT29Column2Block1133,dataT29Column2Block1134,Block.length]

theorem checked328 : checkBlocks (fun n => n/512 ^^^ n%512) 158720 group328 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group329 : List Block := [dataT29Column2Block1135,dataT29Column2Block1136]

theorem length329 : (group329.map Block.length).sum = 512 := by
  simp [group329,dataT29Column2Block1135,dataT29Column2Block1136,Block.length]

theorem checked329 : checkBlocks (fun n => n/512 ^^^ n%512) 159232 group329 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group330 : List Block := [dataT29Column2Block1137,dataT29Column2Block1138]

theorem length330 : (group330.map Block.length).sum = 512 := by
  simp [group330,dataT29Column2Block1137,dataT29Column2Block1138,Block.length]

theorem checked330 : checkBlocks (fun n => n/512 ^^^ n%512) 159744 group330 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group331 : List Block := [dataT29Column2Block1139,dataT29Column2Block1140]

theorem length331 : (group331.map Block.length).sum = 512 := by
  simp [group331,dataT29Column2Block1139,dataT29Column2Block1140,Block.length]

theorem checked331 : checkBlocks (fun n => n/512 ^^^ n%512) 160256 group331 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
