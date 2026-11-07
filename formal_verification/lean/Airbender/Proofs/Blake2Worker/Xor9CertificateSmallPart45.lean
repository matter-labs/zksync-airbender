import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group212 : List Block := [dataT29Column2Block902,dataT29Column2Block903]

theorem length212 : (group212.map Block.length).sum = 512 := by
  simp [group212,dataT29Column2Block902,dataT29Column2Block903,Block.length]

theorem checked212 : checkBlocks (fun n => n/512 ^^^ n%512) 99584 group212 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group213 : List Block := [dataT29Column2Block904,dataT29Column2Block905]

theorem length213 : (group213.map Block.length).sum = 512 := by
  simp [group213,dataT29Column2Block904,dataT29Column2Block905,Block.length]

theorem checked213 : checkBlocks (fun n => n/512 ^^^ n%512) 100096 group213 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group214 : List Block := [dataT29Column2Block906,dataT29Column2Block907]

theorem length214 : (group214.map Block.length).sum = 512 := by
  simp [group214,dataT29Column2Block906,dataT29Column2Block907,Block.length]

theorem checked214 : checkBlocks (fun n => n/512 ^^^ n%512) 100608 group214 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group215 : List Block := [dataT29Column2Block908,dataT29Column2Block909]

theorem length215 : (group215.map Block.length).sum = 512 := by
  simp [group215,dataT29Column2Block908,dataT29Column2Block909,Block.length]

theorem checked215 : checkBlocks (fun n => n/512 ^^^ n%512) 101120 group215 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
