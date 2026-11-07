import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group144 : List Block := [dataT29Column2Block384,dataT29Column2Block385,dataT29Column2Block386,dataT29Column2Block387,dataT29Column2Block388,dataT29Column2Block389,dataT29Column2Block390,dataT29Column2Block391]

theorem length144 : (group144.map Block.length).sum = 64 := by
  simp [group144,dataT29Column2Block384,dataT29Column2Block385,dataT29Column2Block386,dataT29Column2Block387,dataT29Column2Block388,dataT29Column2Block389,dataT29Column2Block390,dataT29Column2Block391,Block.length]

theorem checked144 : checkBlocks (fun n => n/512 ^^^ n%512) 86016 group144 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group145 : List Block := [dataT29Column2Block392,dataT29Column2Block393,dataT29Column2Block394,dataT29Column2Block395,dataT29Column2Block396,dataT29Column2Block397,dataT29Column2Block398,dataT29Column2Block399]

theorem length145 : (group145.map Block.length).sum = 64 := by
  simp [group145,dataT29Column2Block392,dataT29Column2Block393,dataT29Column2Block394,dataT29Column2Block395,dataT29Column2Block396,dataT29Column2Block397,dataT29Column2Block398,dataT29Column2Block399,Block.length]

theorem checked145 : checkBlocks (fun n => n/512 ^^^ n%512) 86080 group145 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group146 : List Block := [dataT29Column2Block400,dataT29Column2Block401,dataT29Column2Block402,dataT29Column2Block403,dataT29Column2Block404,dataT29Column2Block405,dataT29Column2Block406,dataT29Column2Block407]

theorem length146 : (group146.map Block.length).sum = 64 := by
  simp [group146,dataT29Column2Block400,dataT29Column2Block401,dataT29Column2Block402,dataT29Column2Block403,dataT29Column2Block404,dataT29Column2Block405,dataT29Column2Block406,dataT29Column2Block407,Block.length]

theorem checked146 : checkBlocks (fun n => n/512 ^^^ n%512) 86144 group146 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group147 : List Block := [dataT29Column2Block408,dataT29Column2Block409,dataT29Column2Block410,dataT29Column2Block411,dataT29Column2Block412,dataT29Column2Block413,dataT29Column2Block414,dataT29Column2Block415]

theorem length147 : (group147.map Block.length).sum = 64 := by
  simp [group147,dataT29Column2Block408,dataT29Column2Block409,dataT29Column2Block410,dataT29Column2Block411,dataT29Column2Block412,dataT29Column2Block413,dataT29Column2Block414,dataT29Column2Block415,Block.length]

theorem checked147 : checkBlocks (fun n => n/512 ^^^ n%512) 86208 group147 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
