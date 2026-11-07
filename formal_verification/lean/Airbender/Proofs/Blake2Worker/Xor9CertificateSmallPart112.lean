import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group480 : List Block := [dataT29Column2Block1950]

theorem length480 : (group480.map Block.length).sum = 512 := by
  simp [group480,dataT29Column2Block1950,Block.length]

theorem checked480 : checkBlocks (fun n => n/512 ^^^ n%512) 210944 group480 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group481 : List Block := [dataT29Column2Block1951]

theorem length481 : (group481.map Block.length).sum = 512 := by
  simp [group481,dataT29Column2Block1951,Block.length]

theorem checked481 : checkBlocks (fun n => n/512 ^^^ n%512) 211456 group481 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group482 : List Block := [dataT29Column2Block1952]

theorem length482 : (group482.map Block.length).sum = 512 := by
  simp [group482,dataT29Column2Block1952,Block.length]

theorem checked482 : checkBlocks (fun n => n/512 ^^^ n%512) 211968 group482 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group483 : List Block := [dataT29Column2Block1953]

theorem length483 : (group483.map Block.length).sum = 512 := by
  simp [group483,dataT29Column2Block1953,Block.length]

theorem checked483 : checkBlocks (fun n => n/512 ^^^ n%512) 212480 group483 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
