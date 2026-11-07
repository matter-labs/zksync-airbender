import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group332 : List Block := [dataT29Column2Block1141,dataT29Column2Block1142]

theorem length332 : (group332.map Block.length).sum = 512 := by
  simp [group332,dataT29Column2Block1141,dataT29Column2Block1142,Block.length]

theorem checked332 : checkBlocks (fun n => n/512 ^^^ n%512) 160768 group332 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group333 : List Block := [dataT29Column2Block1143,dataT29Column2Block1144]

theorem length333 : (group333.map Block.length).sum = 512 := by
  simp [group333,dataT29Column2Block1143,dataT29Column2Block1144,Block.length]

theorem checked333 : checkBlocks (fun n => n/512 ^^^ n%512) 161280 group333 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group334 : List Block := [dataT29Column2Block1145,dataT29Column2Block1146]

theorem length334 : (group334.map Block.length).sum = 512 := by
  simp [group334,dataT29Column2Block1145,dataT29Column2Block1146,Block.length]

theorem checked334 : checkBlocks (fun n => n/512 ^^^ n%512) 161792 group334 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group335 : List Block := [dataT29Column2Block1147,dataT29Column2Block1148]

theorem length335 : (group335.map Block.length).sum = 512 := by
  simp [group335,dataT29Column2Block1147,dataT29Column2Block1148,Block.length]

theorem checked335 : checkBlocks (fun n => n/512 ^^^ n%512) 162304 group335 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
