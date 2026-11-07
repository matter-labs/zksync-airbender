import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group216 : List Block := [dataT29Column2Block910,dataT29Column2Block911]

theorem length216 : (group216.map Block.length).sum = 512 := by
  simp [group216,dataT29Column2Block910,dataT29Column2Block911,Block.length]

theorem checked216 : checkBlocks (fun n => n/512 ^^^ n%512) 101632 group216 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group217 : List Block := [dataT29Column2Block912,dataT29Column2Block913]

theorem length217 : (group217.map Block.length).sum = 512 := by
  simp [group217,dataT29Column2Block912,dataT29Column2Block913,Block.length]

theorem checked217 : checkBlocks (fun n => n/512 ^^^ n%512) 102144 group217 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group218 : List Block := [dataT29Column2Block914,dataT29Column2Block915]

theorem length218 : (group218.map Block.length).sum = 512 := by
  simp [group218,dataT29Column2Block914,dataT29Column2Block915,Block.length]

theorem checked218 : checkBlocks (fun n => n/512 ^^^ n%512) 102656 group218 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group219 : List Block := [dataT29Column2Block916,dataT29Column2Block917]

theorem length219 : (group219.map Block.length).sum = 512 := by
  simp [group219,dataT29Column2Block916,dataT29Column2Block917,Block.length]

theorem checked219 : checkBlocks (fun n => n/512 ^^^ n%512) 103168 group219 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
