import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group460 : List Block := [dataT29Column2Block1930]

theorem length460 : (group460.map Block.length).sum = 512 := by
  simp [group460,dataT29Column2Block1930,Block.length]

theorem checked460 : checkBlocks (fun n => n/512 ^^^ n%512) 200704 group460 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group461 : List Block := [dataT29Column2Block1931]

theorem length461 : (group461.map Block.length).sum = 512 := by
  simp [group461,dataT29Column2Block1931,Block.length]

theorem checked461 : checkBlocks (fun n => n/512 ^^^ n%512) 201216 group461 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group462 : List Block := [dataT29Column2Block1932]

theorem length462 : (group462.map Block.length).sum = 512 := by
  simp [group462,dataT29Column2Block1932,Block.length]

theorem checked462 : checkBlocks (fun n => n/512 ^^^ n%512) 201728 group462 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group463 : List Block := [dataT29Column2Block1933]

theorem length463 : (group463.map Block.length).sum = 512 := by
  simp [group463,dataT29Column2Block1933,Block.length]

theorem checked463 : checkBlocks (fun n => n/512 ^^^ n%512) 202240 group463 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
