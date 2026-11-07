import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group512 : List Block := [dataT29Column2Block1982]

theorem length512 : (group512.map Block.length).sum = 512 := by
  simp [group512,dataT29Column2Block1982,Block.length]

theorem checked512 : checkBlocks (fun n => n/512 ^^^ n%512) 227328 group512 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group513 : List Block := [dataT29Column2Block1983]

theorem length513 : (group513.map Block.length).sum = 512 := by
  simp [group513,dataT29Column2Block1983,Block.length]

theorem checked513 : checkBlocks (fun n => n/512 ^^^ n%512) 227840 group513 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group514 : List Block := [dataT29Column2Block1984]

theorem length514 : (group514.map Block.length).sum = 512 := by
  simp [group514,dataT29Column2Block1984,Block.length]

theorem checked514 : checkBlocks (fun n => n/512 ^^^ n%512) 228352 group514 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group515 : List Block := [dataT29Column2Block1985]

theorem length515 : (group515.map Block.length).sum = 512 := by
  simp [group515,dataT29Column2Block1985,Block.length]

theorem checked515 : checkBlocks (fun n => n/512 ^^^ n%512) 228864 group515 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
