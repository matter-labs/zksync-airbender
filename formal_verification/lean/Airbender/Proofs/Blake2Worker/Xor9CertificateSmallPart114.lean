import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group488 : List Block := [dataT29Column2Block1958]

theorem length488 : (group488.map Block.length).sum = 512 := by
  simp [group488,dataT29Column2Block1958,Block.length]

theorem checked488 : checkBlocks (fun n => n/512 ^^^ n%512) 215040 group488 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group489 : List Block := [dataT29Column2Block1959]

theorem length489 : (group489.map Block.length).sum = 512 := by
  simp [group489,dataT29Column2Block1959,Block.length]

theorem checked489 : checkBlocks (fun n => n/512 ^^^ n%512) 215552 group489 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group490 : List Block := [dataT29Column2Block1960]

theorem length490 : (group490.map Block.length).sum = 512 := by
  simp [group490,dataT29Column2Block1960,Block.length]

theorem checked490 : checkBlocks (fun n => n/512 ^^^ n%512) 216064 group490 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group491 : List Block := [dataT29Column2Block1961]

theorem length491 : (group491.map Block.length).sum = 512 := by
  simp [group491,dataT29Column2Block1961,Block.length]

theorem checked491 : checkBlocks (fun n => n/512 ^^^ n%512) 216576 group491 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
