import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group316 : List Block := [dataT29Column2Block1109,dataT29Column2Block1110]

theorem length316 : (group316.map Block.length).sum = 512 := by
  simp [group316,dataT29Column2Block1109,dataT29Column2Block1110,Block.length]

theorem checked316 : checkBlocks (fun n => n/512 ^^^ n%512) 152576 group316 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group317 : List Block := [dataT29Column2Block1111,dataT29Column2Block1112]

theorem length317 : (group317.map Block.length).sum = 512 := by
  simp [group317,dataT29Column2Block1111,dataT29Column2Block1112,Block.length]

theorem checked317 : checkBlocks (fun n => n/512 ^^^ n%512) 153088 group317 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group318 : List Block := [dataT29Column2Block1113,dataT29Column2Block1114]

theorem length318 : (group318.map Block.length).sum = 512 := by
  simp [group318,dataT29Column2Block1113,dataT29Column2Block1114,Block.length]

theorem checked318 : checkBlocks (fun n => n/512 ^^^ n%512) 153600 group318 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group319 : List Block := [dataT29Column2Block1115,dataT29Column2Block1116]

theorem length319 : (group319.map Block.length).sum = 512 := by
  simp [group319,dataT29Column2Block1115,dataT29Column2Block1116,Block.length]

theorem checked319 : checkBlocks (fun n => n/512 ^^^ n%512) 154112 group319 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
