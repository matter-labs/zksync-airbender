import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group0 : List Block := [dataT29Column2Block0,dataT29Column2Block1]

theorem length0 : (group0.map Block.length).sum = 1024 := by
  simp [group0,dataT29Column2Block0,dataT29Column2Block1,Block.length]

theorem checked0 : checkBlocks (fun n => n/512 ^^^ n%512) 0 group0 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group1 : List Block := [dataT29Column2Block2,dataT29Column2Block3]

theorem length1 : (group1.map Block.length).sum = 1024 := by
  simp [group1,dataT29Column2Block2,dataT29Column2Block3,Block.length]

theorem checked1 : checkBlocks (fun n => n/512 ^^^ n%512) 1024 group1 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group2 : List Block := [dataT29Column2Block4,dataT29Column2Block5]

theorem length2 : (group2.map Block.length).sum = 1024 := by
  simp [group2,dataT29Column2Block4,dataT29Column2Block5,Block.length]

theorem checked2 : checkBlocks (fun n => n/512 ^^^ n%512) 2048 group2 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group3 : List Block := [dataT29Column2Block6,dataT29Column2Block7]

theorem length3 : (group3.map Block.length).sum = 1024 := by
  simp [group3,dataT29Column2Block6,dataT29Column2Block7,Block.length]

theorem checked3 : checkBlocks (fun n => n/512 ^^^ n%512) 3072 group3 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
