import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group476 : List Block := [dataT29Column2Block1946]

theorem length476 : (group476.map Block.length).sum = 512 := by
  simp [group476,dataT29Column2Block1946,Block.length]

theorem checked476 : checkBlocks (fun n => n/512 ^^^ n%512) 208896 group476 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group477 : List Block := [dataT29Column2Block1947]

theorem length477 : (group477.map Block.length).sum = 512 := by
  simp [group477,dataT29Column2Block1947,Block.length]

theorem checked477 : checkBlocks (fun n => n/512 ^^^ n%512) 209408 group477 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group478 : List Block := [dataT29Column2Block1948]

theorem length478 : (group478.map Block.length).sum = 512 := by
  simp [group478,dataT29Column2Block1948,Block.length]

theorem checked478 : checkBlocks (fun n => n/512 ^^^ n%512) 209920 group478 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group479 : List Block := [dataT29Column2Block1949]

theorem length479 : (group479.map Block.length).sum = 512 := by
  simp [group479,dataT29Column2Block1949,Block.length]

theorem checked479 : checkBlocks (fun n => n/512 ^^^ n%512) 210432 group479 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
