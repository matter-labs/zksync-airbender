import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group256 : List Block := [dataT29Column2Block990,dataT29Column2Block991]

theorem length256 : (group256.map Block.length).sum = 512 := by
  simp [group256,dataT29Column2Block990,dataT29Column2Block991,Block.length]

theorem checked256 : checkBlocks (fun n => n/512 ^^^ n%512) 122112 group256 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group257 : List Block := [dataT29Column2Block992,dataT29Column2Block993]

theorem length257 : (group257.map Block.length).sum = 512 := by
  simp [group257,dataT29Column2Block992,dataT29Column2Block993,Block.length]

theorem checked257 : checkBlocks (fun n => n/512 ^^^ n%512) 122624 group257 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group258 : List Block := [dataT29Column2Block994,dataT29Column2Block995]

theorem length258 : (group258.map Block.length).sum = 512 := by
  simp [group258,dataT29Column2Block994,dataT29Column2Block995,Block.length]

theorem checked258 : checkBlocks (fun n => n/512 ^^^ n%512) 123136 group258 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group259 : List Block := [dataT29Column2Block996,dataT29Column2Block997]

theorem length259 : (group259.map Block.length).sum = 512 := by
  simp [group259,dataT29Column2Block996,dataT29Column2Block997,Block.length]

theorem checked259 : checkBlocks (fun n => n/512 ^^^ n%512) 123648 group259 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
