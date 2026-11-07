import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group64 : List Block := [dataT29Column2Block96]

theorem length64 : (group64.map Block.length).sum = 512 := by
  simp [group64,dataT29Column2Block96,Block.length]

theorem checked64 : checkBlocks (fun n => n/512 ^^^ n%512) 49152 group64 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group65 : List Block := [dataT29Column2Block97]

theorem length65 : (group65.map Block.length).sum = 512 := by
  simp [group65,dataT29Column2Block97,Block.length]

theorem checked65 : checkBlocks (fun n => n/512 ^^^ n%512) 49664 group65 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group66 : List Block := [dataT29Column2Block98]

theorem length66 : (group66.map Block.length).sum = 512 := by
  simp [group66,dataT29Column2Block98,Block.length]

theorem checked66 : checkBlocks (fun n => n/512 ^^^ n%512) 50176 group66 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group67 : List Block := [dataT29Column2Block99]

theorem length67 : (group67.map Block.length).sum = 512 := by
  simp [group67,dataT29Column2Block99,Block.length]

theorem checked67 : checkBlocks (fun n => n/512 ^^^ n%512) 50688 group67 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
