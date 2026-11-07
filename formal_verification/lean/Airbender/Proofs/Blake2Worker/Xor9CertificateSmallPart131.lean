import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group556 : List Block := [dataT29Column2Block2026]

theorem length556 : (group556.map Block.length).sum = 512 := by
  simp [group556,dataT29Column2Block2026,Block.length]

theorem checked556 : checkBlocks (fun n => n/512 ^^^ n%512) 249856 group556 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group557 : List Block := [dataT29Column2Block2027]

theorem length557 : (group557.map Block.length).sum = 512 := by
  simp [group557,dataT29Column2Block2027,Block.length]

theorem checked557 : checkBlocks (fun n => n/512 ^^^ n%512) 250368 group557 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group558 : List Block := [dataT29Column2Block2028]

theorem length558 : (group558.map Block.length).sum = 512 := by
  simp [group558,dataT29Column2Block2028,Block.length]

theorem checked558 : checkBlocks (fun n => n/512 ^^^ n%512) 250880 group558 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group559 : List Block := [dataT29Column2Block2029]

theorem length559 : (group559.map Block.length).sum = 512 := by
  simp [group559,dataT29Column2Block2029,Block.length]

theorem checked559 : checkBlocks (fun n => n/512 ^^^ n%512) 251392 group559 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
