import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group140 : List Block := [dataT29Column2Block352,dataT29Column2Block353,dataT29Column2Block354,dataT29Column2Block355,dataT29Column2Block356,dataT29Column2Block357,dataT29Column2Block358,dataT29Column2Block359]

theorem length140 : (group140.map Block.length).sum = 256 := by
  simp [group140,dataT29Column2Block352,dataT29Column2Block353,dataT29Column2Block354,dataT29Column2Block355,dataT29Column2Block356,dataT29Column2Block357,dataT29Column2Block358,dataT29Column2Block359,Block.length]

theorem checked140 : checkBlocks (fun n => n/512 ^^^ n%512) 84992 group140 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group141 : List Block := [dataT29Column2Block360,dataT29Column2Block361,dataT29Column2Block362,dataT29Column2Block363,dataT29Column2Block364,dataT29Column2Block365,dataT29Column2Block366,dataT29Column2Block367]

theorem length141 : (group141.map Block.length).sum = 256 := by
  simp [group141,dataT29Column2Block360,dataT29Column2Block361,dataT29Column2Block362,dataT29Column2Block363,dataT29Column2Block364,dataT29Column2Block365,dataT29Column2Block366,dataT29Column2Block367,Block.length]

theorem checked141 : checkBlocks (fun n => n/512 ^^^ n%512) 85248 group141 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group142 : List Block := [dataT29Column2Block368,dataT29Column2Block369,dataT29Column2Block370,dataT29Column2Block371,dataT29Column2Block372,dataT29Column2Block373,dataT29Column2Block374,dataT29Column2Block375]

theorem length142 : (group142.map Block.length).sum = 256 := by
  simp [group142,dataT29Column2Block368,dataT29Column2Block369,dataT29Column2Block370,dataT29Column2Block371,dataT29Column2Block372,dataT29Column2Block373,dataT29Column2Block374,dataT29Column2Block375,Block.length]

theorem checked142 : checkBlocks (fun n => n/512 ^^^ n%512) 85504 group142 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group143 : List Block := [dataT29Column2Block376,dataT29Column2Block377,dataT29Column2Block378,dataT29Column2Block379,dataT29Column2Block380,dataT29Column2Block381,dataT29Column2Block382,dataT29Column2Block383]

theorem length143 : (group143.map Block.length).sum = 256 := by
  simp [group143,dataT29Column2Block376,dataT29Column2Block377,dataT29Column2Block378,dataT29Column2Block379,dataT29Column2Block380,dataT29Column2Block381,dataT29Column2Block382,dataT29Column2Block383,Block.length]

theorem checked143 : checkBlocks (fun n => n/512 ^^^ n%512) 85760 group143 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
