import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group264 : List Block := [dataT29Column2Block1006,dataT29Column2Block1007]

theorem length264 : (group264.map Block.length).sum = 512 := by
  simp [group264,dataT29Column2Block1006,dataT29Column2Block1007,Block.length]

theorem checked264 : checkBlocks (fun n => n/512 ^^^ n%512) 126208 group264 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group265 : List Block := [dataT29Column2Block1008,dataT29Column2Block1009]

theorem length265 : (group265.map Block.length).sum = 512 := by
  simp [group265,dataT29Column2Block1008,dataT29Column2Block1009,Block.length]

theorem checked265 : checkBlocks (fun n => n/512 ^^^ n%512) 126720 group265 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group266 : List Block := [dataT29Column2Block1010,dataT29Column2Block1011]

theorem length266 : (group266.map Block.length).sum = 512 := by
  simp [group266,dataT29Column2Block1010,dataT29Column2Block1011,Block.length]

theorem checked266 : checkBlocks (fun n => n/512 ^^^ n%512) 127232 group266 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group267 : List Block := [dataT29Column2Block1012,dataT29Column2Block1013]

theorem length267 : (group267.map Block.length).sum = 512 := by
  simp [group267,dataT29Column2Block1012,dataT29Column2Block1013,Block.length]

theorem checked267 : checkBlocks (fun n => n/512 ^^^ n%512) 127744 group267 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
