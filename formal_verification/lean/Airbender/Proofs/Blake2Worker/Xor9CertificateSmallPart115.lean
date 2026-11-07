import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group492 : List Block := [dataT29Column2Block1962]

theorem length492 : (group492.map Block.length).sum = 512 := by
  simp [group492,dataT29Column2Block1962,Block.length]

theorem checked492 : checkBlocks (fun n => n/512 ^^^ n%512) 217088 group492 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group493 : List Block := [dataT29Column2Block1963]

theorem length493 : (group493.map Block.length).sum = 512 := by
  simp [group493,dataT29Column2Block1963,Block.length]

theorem checked493 : checkBlocks (fun n => n/512 ^^^ n%512) 217600 group493 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group494 : List Block := [dataT29Column2Block1964]

theorem length494 : (group494.map Block.length).sum = 512 := by
  simp [group494,dataT29Column2Block1964,Block.length]

theorem checked494 : checkBlocks (fun n => n/512 ^^^ n%512) 218112 group494 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group495 : List Block := [dataT29Column2Block1965]

theorem length495 : (group495.map Block.length).sum = 512 := by
  simp [group495,dataT29Column2Block1965,Block.length]

theorem checked495 : checkBlocks (fun n => n/512 ^^^ n%512) 218624 group495 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
