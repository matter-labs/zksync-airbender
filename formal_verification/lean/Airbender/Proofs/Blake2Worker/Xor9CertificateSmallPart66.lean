import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group296 : List Block := [dataT29Column2Block1069,dataT29Column2Block1070]

theorem length296 : (group296.map Block.length).sum = 512 := by
  simp [group296,dataT29Column2Block1069,dataT29Column2Block1070,Block.length]

theorem checked296 : checkBlocks (fun n => n/512 ^^^ n%512) 142336 group296 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group297 : List Block := [dataT29Column2Block1071,dataT29Column2Block1072]

theorem length297 : (group297.map Block.length).sum = 512 := by
  simp [group297,dataT29Column2Block1071,dataT29Column2Block1072,Block.length]

theorem checked297 : checkBlocks (fun n => n/512 ^^^ n%512) 142848 group297 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group298 : List Block := [dataT29Column2Block1073,dataT29Column2Block1074]

theorem length298 : (group298.map Block.length).sum = 512 := by
  simp [group298,dataT29Column2Block1073,dataT29Column2Block1074,Block.length]

theorem checked298 : checkBlocks (fun n => n/512 ^^^ n%512) 143360 group298 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group299 : List Block := [dataT29Column2Block1075,dataT29Column2Block1076]

theorem length299 : (group299.map Block.length).sum = 512 := by
  simp [group299,dataT29Column2Block1075,dataT29Column2Block1076,Block.length]

theorem checked299 : checkBlocks (fun n => n/512 ^^^ n%512) 143872 group299 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
