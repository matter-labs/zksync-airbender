import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group572 : List Block := [dataT29Column2Block2042]

theorem length572 : (group572.map Block.length).sum = 512 := by
  simp [group572,dataT29Column2Block2042,Block.length]

theorem checked572 : checkBlocks (fun n => n/512 ^^^ n%512) 258048 group572 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group573 : List Block := [dataT29Column2Block2043]

theorem length573 : (group573.map Block.length).sum = 512 := by
  simp [group573,dataT29Column2Block2043,Block.length]

theorem checked573 : checkBlocks (fun n => n/512 ^^^ n%512) 258560 group573 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group574 : List Block := [dataT29Column2Block2044]

theorem length574 : (group574.map Block.length).sum = 512 := by
  simp [group574,dataT29Column2Block2044,Block.length]

theorem checked574 : checkBlocks (fun n => n/512 ^^^ n%512) 259072 group574 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group575 : List Block := [dataT29Column2Block2045]

theorem length575 : (group575.map Block.length).sum = 512 := by
  simp [group575,dataT29Column2Block2045,Block.length]

theorem checked575 : checkBlocks (fun n => n/512 ^^^ n%512) 259584 group575 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
