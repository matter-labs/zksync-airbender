import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group32 : List Block := [dataT29Column2Block64]

theorem length32 : (group32.map Block.length).sum = 512 := by
  simp [group32,dataT29Column2Block64,Block.length]

theorem checked32 : checkBlocks (fun n => n/512 ^^^ n%512) 32768 group32 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group33 : List Block := [dataT29Column2Block65]

theorem length33 : (group33.map Block.length).sum = 512 := by
  simp [group33,dataT29Column2Block65,Block.length]

theorem checked33 : checkBlocks (fun n => n/512 ^^^ n%512) 33280 group33 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group34 : List Block := [dataT29Column2Block66]

theorem length34 : (group34.map Block.length).sum = 512 := by
  simp [group34,dataT29Column2Block66,Block.length]

theorem checked34 : checkBlocks (fun n => n/512 ^^^ n%512) 33792 group34 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group35 : List Block := [dataT29Column2Block67]

theorem length35 : (group35.map Block.length).sum = 512 := by
  simp [group35,dataT29Column2Block67,Block.length]

theorem checked35 : checkBlocks (fun n => n/512 ^^^ n%512) 34304 group35 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
