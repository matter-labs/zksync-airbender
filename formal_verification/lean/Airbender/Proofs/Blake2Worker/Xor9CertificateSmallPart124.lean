import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group528 : List Block := [dataT29Column2Block1998]

theorem length528 : (group528.map Block.length).sum = 512 := by
  simp [group528,dataT29Column2Block1998,Block.length]

theorem checked528 : checkBlocks (fun n => n/512 ^^^ n%512) 235520 group528 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group529 : List Block := [dataT29Column2Block1999]

theorem length529 : (group529.map Block.length).sum = 512 := by
  simp [group529,dataT29Column2Block1999,Block.length]

theorem checked529 : checkBlocks (fun n => n/512 ^^^ n%512) 236032 group529 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group530 : List Block := [dataT29Column2Block2000]

theorem length530 : (group530.map Block.length).sum = 512 := by
  simp [group530,dataT29Column2Block2000,Block.length]

theorem checked530 : checkBlocks (fun n => n/512 ^^^ n%512) 236544 group530 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group531 : List Block := [dataT29Column2Block2001]

theorem length531 : (group531.map Block.length).sum = 512 := by
  simp [group531,dataT29Column2Block2001,Block.length]

theorem checked531 : checkBlocks (fun n => n/512 ^^^ n%512) 237056 group531 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
