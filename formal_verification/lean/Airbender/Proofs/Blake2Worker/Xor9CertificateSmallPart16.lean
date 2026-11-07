import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group96 : List Block := [dataT29Column2Block128,dataT29Column2Block129,dataT29Column2Block130,dataT29Column2Block131]

theorem length96 : (group96.map Block.length).sum = 512 := by
  simp [group96,dataT29Column2Block128,dataT29Column2Block129,dataT29Column2Block130,dataT29Column2Block131,Block.length]

theorem checked96 : checkBlocks (fun n => n/512 ^^^ n%512) 65536 group96 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group97 : List Block := [dataT29Column2Block132,dataT29Column2Block133,dataT29Column2Block134,dataT29Column2Block135]

theorem length97 : (group97.map Block.length).sum = 512 := by
  simp [group97,dataT29Column2Block132,dataT29Column2Block133,dataT29Column2Block134,dataT29Column2Block135,Block.length]

theorem checked97 : checkBlocks (fun n => n/512 ^^^ n%512) 66048 group97 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group98 : List Block := [dataT29Column2Block136,dataT29Column2Block137,dataT29Column2Block138,dataT29Column2Block139]

theorem length98 : (group98.map Block.length).sum = 512 := by
  simp [group98,dataT29Column2Block136,dataT29Column2Block137,dataT29Column2Block138,dataT29Column2Block139,Block.length]

theorem checked98 : checkBlocks (fun n => n/512 ^^^ n%512) 66560 group98 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group99 : List Block := [dataT29Column2Block140,dataT29Column2Block141,dataT29Column2Block142,dataT29Column2Block143]

theorem length99 : (group99.map Block.length).sum = 512 := by
  simp [group99,dataT29Column2Block140,dataT29Column2Block141,dataT29Column2Block142,dataT29Column2Block143,Block.length]

theorem checked99 : checkBlocks (fun n => n/512 ^^^ n%512) 67072 group99 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
