import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group80 : List Block := [dataT29Column2Block112]

theorem length80 : (group80.map Block.length).sum = 512 := by
  simp [group80,dataT29Column2Block112,Block.length]

theorem checked80 : checkBlocks (fun n => n/512 ^^^ n%512) 57344 group80 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group81 : List Block := [dataT29Column2Block113]

theorem length81 : (group81.map Block.length).sum = 512 := by
  simp [group81,dataT29Column2Block113,Block.length]

theorem checked81 : checkBlocks (fun n => n/512 ^^^ n%512) 57856 group81 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group82 : List Block := [dataT29Column2Block114]

theorem length82 : (group82.map Block.length).sum = 512 := by
  simp [group82,dataT29Column2Block114,Block.length]

theorem checked82 : checkBlocks (fun n => n/512 ^^^ n%512) 58368 group82 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group83 : List Block := [dataT29Column2Block115]

theorem length83 : (group83.map Block.length).sum = 512 := by
  simp [group83,dataT29Column2Block115,Block.length]

theorem checked83 : checkBlocks (fun n => n/512 ^^^ n%512) 58880 group83 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
