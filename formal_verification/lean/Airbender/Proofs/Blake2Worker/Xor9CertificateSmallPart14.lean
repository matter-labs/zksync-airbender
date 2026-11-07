import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group88 : List Block := [dataT29Column2Block120]

theorem length88 : (group88.map Block.length).sum = 512 := by
  simp [group88,dataT29Column2Block120,Block.length]

theorem checked88 : checkBlocks (fun n => n/512 ^^^ n%512) 61440 group88 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group89 : List Block := [dataT29Column2Block121]

theorem length89 : (group89.map Block.length).sum = 512 := by
  simp [group89,dataT29Column2Block121,Block.length]

theorem checked89 : checkBlocks (fun n => n/512 ^^^ n%512) 61952 group89 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group90 : List Block := [dataT29Column2Block122]

theorem length90 : (group90.map Block.length).sum = 512 := by
  simp [group90,dataT29Column2Block122,Block.length]

theorem checked90 : checkBlocks (fun n => n/512 ^^^ n%512) 62464 group90 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group91 : List Block := [dataT29Column2Block123]

theorem length91 : (group91.map Block.length).sum = 512 := by
  simp [group91,dataT29Column2Block123,Block.length]

theorem checked91 : checkBlocks (fun n => n/512 ^^^ n%512) 62976 group91 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
