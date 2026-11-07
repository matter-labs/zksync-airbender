import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group252 : List Block := [dataT29Column2Block982,dataT29Column2Block983]

theorem length252 : (group252.map Block.length).sum = 512 := by
  simp [group252,dataT29Column2Block982,dataT29Column2Block983,Block.length]

theorem checked252 : checkBlocks (fun n => n/512 ^^^ n%512) 120064 group252 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group253 : List Block := [dataT29Column2Block984,dataT29Column2Block985]

theorem length253 : (group253.map Block.length).sum = 512 := by
  simp [group253,dataT29Column2Block984,dataT29Column2Block985,Block.length]

theorem checked253 : checkBlocks (fun n => n/512 ^^^ n%512) 120576 group253 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group254 : List Block := [dataT29Column2Block986,dataT29Column2Block987]

theorem length254 : (group254.map Block.length).sum = 512 := by
  simp [group254,dataT29Column2Block986,dataT29Column2Block987,Block.length]

theorem checked254 : checkBlocks (fun n => n/512 ^^^ n%512) 121088 group254 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group255 : List Block := [dataT29Column2Block988,dataT29Column2Block989]

theorem length255 : (group255.map Block.length).sum = 512 := by
  simp [group255,dataT29Column2Block988,dataT29Column2Block989,Block.length]

theorem checked255 : checkBlocks (fun n => n/512 ^^^ n%512) 121600 group255 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
