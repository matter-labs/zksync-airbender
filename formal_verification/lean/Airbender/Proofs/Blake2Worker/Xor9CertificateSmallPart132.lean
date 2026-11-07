import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group560 : List Block := [dataT29Column2Block2030]

theorem length560 : (group560.map Block.length).sum = 512 := by
  simp [group560,dataT29Column2Block2030,Block.length]

theorem checked560 : checkBlocks (fun n => n/512 ^^^ n%512) 251904 group560 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group561 : List Block := [dataT29Column2Block2031]

theorem length561 : (group561.map Block.length).sum = 512 := by
  simp [group561,dataT29Column2Block2031,Block.length]

theorem checked561 : checkBlocks (fun n => n/512 ^^^ n%512) 252416 group561 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group562 : List Block := [dataT29Column2Block2032]

theorem length562 : (group562.map Block.length).sum = 512 := by
  simp [group562,dataT29Column2Block2032,Block.length]

theorem checked562 : checkBlocks (fun n => n/512 ^^^ n%512) 252928 group562 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group563 : List Block := [dataT29Column2Block2033]

theorem length563 : (group563.map Block.length).sum = 512 := by
  simp [group563,dataT29Column2Block2033,Block.length]

theorem checked563 : checkBlocks (fun n => n/512 ^^^ n%512) 253440 group563 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
