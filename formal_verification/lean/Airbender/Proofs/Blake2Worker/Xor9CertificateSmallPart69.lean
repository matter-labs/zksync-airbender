import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group308 : List Block := [dataT29Column2Block1093,dataT29Column2Block1094]

theorem length308 : (group308.map Block.length).sum = 512 := by
  simp [group308,dataT29Column2Block1093,dataT29Column2Block1094,Block.length]

theorem checked308 : checkBlocks (fun n => n/512 ^^^ n%512) 148480 group308 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group309 : List Block := [dataT29Column2Block1095,dataT29Column2Block1096]

theorem length309 : (group309.map Block.length).sum = 512 := by
  simp [group309,dataT29Column2Block1095,dataT29Column2Block1096,Block.length]

theorem checked309 : checkBlocks (fun n => n/512 ^^^ n%512) 148992 group309 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group310 : List Block := [dataT29Column2Block1097,dataT29Column2Block1098]

theorem length310 : (group310.map Block.length).sum = 512 := by
  simp [group310,dataT29Column2Block1097,dataT29Column2Block1098,Block.length]

theorem checked310 : checkBlocks (fun n => n/512 ^^^ n%512) 149504 group310 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group311 : List Block := [dataT29Column2Block1099,dataT29Column2Block1100]

theorem length311 : (group311.map Block.length).sum = 512 := by
  simp [group311,dataT29Column2Block1099,dataT29Column2Block1100,Block.length]

theorem checked311 : checkBlocks (fun n => n/512 ^^^ n%512) 150016 group311 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
