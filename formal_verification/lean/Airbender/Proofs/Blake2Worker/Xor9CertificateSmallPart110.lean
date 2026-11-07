import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group472 : List Block := [dataT29Column2Block1942]

theorem length472 : (group472.map Block.length).sum = 512 := by
  simp [group472,dataT29Column2Block1942,Block.length]

theorem checked472 : checkBlocks (fun n => n/512 ^^^ n%512) 206848 group472 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group473 : List Block := [dataT29Column2Block1943]

theorem length473 : (group473.map Block.length).sum = 512 := by
  simp [group473,dataT29Column2Block1943,Block.length]

theorem checked473 : checkBlocks (fun n => n/512 ^^^ n%512) 207360 group473 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group474 : List Block := [dataT29Column2Block1944]

theorem length474 : (group474.map Block.length).sum = 512 := by
  simp [group474,dataT29Column2Block1944,Block.length]

theorem checked474 : checkBlocks (fun n => n/512 ^^^ n%512) 207872 group474 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group475 : List Block := [dataT29Column2Block1945]

theorem length475 : (group475.map Block.length).sum = 512 := by
  simp [group475,dataT29Column2Block1945,Block.length]

theorem checked475 : checkBlocks (fun n => n/512 ^^^ n%512) 208384 group475 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
