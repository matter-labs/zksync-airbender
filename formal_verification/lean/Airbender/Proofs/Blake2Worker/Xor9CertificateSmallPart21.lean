import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group116 : List Block := [dataT29Column2Block208,dataT29Column2Block209,dataT29Column2Block210,dataT29Column2Block211]

theorem length116 : (group116.map Block.length).sum = 512 := by
  simp [group116,dataT29Column2Block208,dataT29Column2Block209,dataT29Column2Block210,dataT29Column2Block211,Block.length]

theorem checked116 : checkBlocks (fun n => n/512 ^^^ n%512) 75776 group116 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group117 : List Block := [dataT29Column2Block212,dataT29Column2Block213,dataT29Column2Block214,dataT29Column2Block215]

theorem length117 : (group117.map Block.length).sum = 512 := by
  simp [group117,dataT29Column2Block212,dataT29Column2Block213,dataT29Column2Block214,dataT29Column2Block215,Block.length]

theorem checked117 : checkBlocks (fun n => n/512 ^^^ n%512) 76288 group117 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group118 : List Block := [dataT29Column2Block216,dataT29Column2Block217,dataT29Column2Block218,dataT29Column2Block219]

theorem length118 : (group118.map Block.length).sum = 512 := by
  simp [group118,dataT29Column2Block216,dataT29Column2Block217,dataT29Column2Block218,dataT29Column2Block219,Block.length]

theorem checked118 : checkBlocks (fun n => n/512 ^^^ n%512) 76800 group118 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group119 : List Block := [dataT29Column2Block220,dataT29Column2Block221,dataT29Column2Block222,dataT29Column2Block223]

theorem length119 : (group119.map Block.length).sum = 512 := by
  simp [group119,dataT29Column2Block220,dataT29Column2Block221,dataT29Column2Block222,dataT29Column2Block223,Block.length]

theorem checked119 : checkBlocks (fun n => n/512 ^^^ n%512) 77312 group119 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
