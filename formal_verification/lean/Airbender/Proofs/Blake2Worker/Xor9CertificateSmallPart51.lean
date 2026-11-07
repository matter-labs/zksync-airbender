import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group236 : List Block := [dataT29Column2Block950,dataT29Column2Block951]

theorem length236 : (group236.map Block.length).sum = 512 := by
  simp [group236,dataT29Column2Block950,dataT29Column2Block951,Block.length]

theorem checked236 : checkBlocks (fun n => n/512 ^^^ n%512) 111872 group236 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group237 : List Block := [dataT29Column2Block952,dataT29Column2Block953]

theorem length237 : (group237.map Block.length).sum = 512 := by
  simp [group237,dataT29Column2Block952,dataT29Column2Block953,Block.length]

theorem checked237 : checkBlocks (fun n => n/512 ^^^ n%512) 112384 group237 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group238 : List Block := [dataT29Column2Block954,dataT29Column2Block955]

theorem length238 : (group238.map Block.length).sum = 512 := by
  simp [group238,dataT29Column2Block954,dataT29Column2Block955,Block.length]

theorem checked238 : checkBlocks (fun n => n/512 ^^^ n%512) 112896 group238 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group239 : List Block := [dataT29Column2Block956,dataT29Column2Block957]

theorem length239 : (group239.map Block.length).sum = 512 := by
  simp [group239,dataT29Column2Block956,dataT29Column2Block957,Block.length]

theorem checked239 : checkBlocks (fun n => n/512 ^^^ n%512) 113408 group239 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
