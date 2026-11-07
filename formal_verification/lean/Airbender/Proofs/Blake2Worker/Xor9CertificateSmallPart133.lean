import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group564 : List Block := [dataT29Column2Block2034]

theorem length564 : (group564.map Block.length).sum = 512 := by
  simp [group564,dataT29Column2Block2034,Block.length]

theorem checked564 : checkBlocks (fun n => n/512 ^^^ n%512) 253952 group564 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group565 : List Block := [dataT29Column2Block2035]

theorem length565 : (group565.map Block.length).sum = 512 := by
  simp [group565,dataT29Column2Block2035,Block.length]

theorem checked565 : checkBlocks (fun n => n/512 ^^^ n%512) 254464 group565 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group566 : List Block := [dataT29Column2Block2036]

theorem length566 : (group566.map Block.length).sum = 512 := by
  simp [group566,dataT29Column2Block2036,Block.length]

theorem checked566 : checkBlocks (fun n => n/512 ^^^ n%512) 254976 group566 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group567 : List Block := [dataT29Column2Block2037]

theorem length567 : (group567.map Block.length).sum = 512 := by
  simp [group567,dataT29Column2Block2037,Block.length]

theorem checked567 : checkBlocks (fun n => n/512 ^^^ n%512) 255488 group567 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
