import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group324 : List Block := [dataT29Column2Block1125,dataT29Column2Block1126]

theorem length324 : (group324.map Block.length).sum = 512 := by
  simp [group324,dataT29Column2Block1125,dataT29Column2Block1126,Block.length]

theorem checked324 : checkBlocks (fun n => n/512 ^^^ n%512) 156672 group324 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group325 : List Block := [dataT29Column2Block1127,dataT29Column2Block1128]

theorem length325 : (group325.map Block.length).sum = 512 := by
  simp [group325,dataT29Column2Block1127,dataT29Column2Block1128,Block.length]

theorem checked325 : checkBlocks (fun n => n/512 ^^^ n%512) 157184 group325 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group326 : List Block := [dataT29Column2Block1129,dataT29Column2Block1130]

theorem length326 : (group326.map Block.length).sum = 512 := by
  simp [group326,dataT29Column2Block1129,dataT29Column2Block1130,Block.length]

theorem checked326 : checkBlocks (fun n => n/512 ^^^ n%512) 157696 group326 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group327 : List Block := [dataT29Column2Block1131,dataT29Column2Block1132]

theorem length327 : (group327.map Block.length).sum = 512 := by
  simp [group327,dataT29Column2Block1131,dataT29Column2Block1132,Block.length]

theorem checked327 : checkBlocks (fun n => n/512 ^^^ n%512) 158208 group327 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
