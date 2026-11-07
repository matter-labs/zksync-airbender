import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group320 : List Block := [dataT29Column2Block1117,dataT29Column2Block1118]

theorem length320 : (group320.map Block.length).sum = 512 := by
  simp [group320,dataT29Column2Block1117,dataT29Column2Block1118,Block.length]

theorem checked320 : checkBlocks (fun n => n/512 ^^^ n%512) 154624 group320 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group321 : List Block := [dataT29Column2Block1119,dataT29Column2Block1120]

theorem length321 : (group321.map Block.length).sum = 512 := by
  simp [group321,dataT29Column2Block1119,dataT29Column2Block1120,Block.length]

theorem checked321 : checkBlocks (fun n => n/512 ^^^ n%512) 155136 group321 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group322 : List Block := [dataT29Column2Block1121,dataT29Column2Block1122]

theorem length322 : (group322.map Block.length).sum = 512 := by
  simp [group322,dataT29Column2Block1121,dataT29Column2Block1122,Block.length]

theorem checked322 : checkBlocks (fun n => n/512 ^^^ n%512) 155648 group322 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group323 : List Block := [dataT29Column2Block1123,dataT29Column2Block1124]

theorem length323 : (group323.map Block.length).sum = 512 := by
  simp [group323,dataT29Column2Block1123,dataT29Column2Block1124,Block.length]

theorem checked323 : checkBlocks (fun n => n/512 ^^^ n%512) 156160 group323 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
