import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group304 : List Block := [dataT29Column2Block1085,dataT29Column2Block1086]

theorem length304 : (group304.map Block.length).sum = 512 := by
  simp [group304,dataT29Column2Block1085,dataT29Column2Block1086,Block.length]

theorem checked304 : checkBlocks (fun n => n/512 ^^^ n%512) 146432 group304 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group305 : List Block := [dataT29Column2Block1087,dataT29Column2Block1088]

theorem length305 : (group305.map Block.length).sum = 512 := by
  simp [group305,dataT29Column2Block1087,dataT29Column2Block1088,Block.length]

theorem checked305 : checkBlocks (fun n => n/512 ^^^ n%512) 146944 group305 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group306 : List Block := [dataT29Column2Block1089,dataT29Column2Block1090]

theorem length306 : (group306.map Block.length).sum = 512 := by
  simp [group306,dataT29Column2Block1089,dataT29Column2Block1090,Block.length]

theorem checked306 : checkBlocks (fun n => n/512 ^^^ n%512) 147456 group306 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group307 : List Block := [dataT29Column2Block1091,dataT29Column2Block1092]

theorem length307 : (group307.map Block.length).sum = 512 := by
  simp [group307,dataT29Column2Block1091,dataT29Column2Block1092,Block.length]

theorem checked307 : checkBlocks (fun n => n/512 ^^^ n%512) 147968 group307 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
