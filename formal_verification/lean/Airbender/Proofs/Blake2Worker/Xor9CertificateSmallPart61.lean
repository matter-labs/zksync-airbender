import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group276 : List Block := [dataT29Column2Block1029,dataT29Column2Block1030]

theorem length276 : (group276.map Block.length).sum = 512 := by
  simp [group276,dataT29Column2Block1029,dataT29Column2Block1030,Block.length]

theorem checked276 : checkBlocks (fun n => n/512 ^^^ n%512) 132096 group276 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group277 : List Block := [dataT29Column2Block1031,dataT29Column2Block1032]

theorem length277 : (group277.map Block.length).sum = 512 := by
  simp [group277,dataT29Column2Block1031,dataT29Column2Block1032,Block.length]

theorem checked277 : checkBlocks (fun n => n/512 ^^^ n%512) 132608 group277 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group278 : List Block := [dataT29Column2Block1033,dataT29Column2Block1034]

theorem length278 : (group278.map Block.length).sum = 512 := by
  simp [group278,dataT29Column2Block1033,dataT29Column2Block1034,Block.length]

theorem checked278 : checkBlocks (fun n => n/512 ^^^ n%512) 133120 group278 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group279 : List Block := [dataT29Column2Block1035,dataT29Column2Block1036]

theorem length279 : (group279.map Block.length).sum = 512 := by
  simp [group279,dataT29Column2Block1035,dataT29Column2Block1036,Block.length]

theorem checked279 : checkBlocks (fun n => n/512 ^^^ n%512) 133632 group279 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
