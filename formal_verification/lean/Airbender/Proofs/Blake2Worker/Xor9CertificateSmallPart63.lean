import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group284 : List Block := [dataT29Column2Block1045,dataT29Column2Block1046]

theorem length284 : (group284.map Block.length).sum = 512 := by
  simp [group284,dataT29Column2Block1045,dataT29Column2Block1046,Block.length]

theorem checked284 : checkBlocks (fun n => n/512 ^^^ n%512) 136192 group284 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group285 : List Block := [dataT29Column2Block1047,dataT29Column2Block1048]

theorem length285 : (group285.map Block.length).sum = 512 := by
  simp [group285,dataT29Column2Block1047,dataT29Column2Block1048,Block.length]

theorem checked285 : checkBlocks (fun n => n/512 ^^^ n%512) 136704 group285 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group286 : List Block := [dataT29Column2Block1049,dataT29Column2Block1050]

theorem length286 : (group286.map Block.length).sum = 512 := by
  simp [group286,dataT29Column2Block1049,dataT29Column2Block1050,Block.length]

theorem checked286 : checkBlocks (fun n => n/512 ^^^ n%512) 137216 group286 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group287 : List Block := [dataT29Column2Block1051,dataT29Column2Block1052]

theorem length287 : (group287.map Block.length).sum = 512 := by
  simp [group287,dataT29Column2Block1051,dataT29Column2Block1052,Block.length]

theorem checked287 : checkBlocks (fun n => n/512 ^^^ n%512) 137728 group287 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
