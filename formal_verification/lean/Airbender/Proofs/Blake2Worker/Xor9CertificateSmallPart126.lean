import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group536 : List Block := [dataT29Column2Block2006]

theorem length536 : (group536.map Block.length).sum = 512 := by
  simp [group536,dataT29Column2Block2006,Block.length]

theorem checked536 : checkBlocks (fun n => n/512 ^^^ n%512) 239616 group536 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group537 : List Block := [dataT29Column2Block2007]

theorem length537 : (group537.map Block.length).sum = 512 := by
  simp [group537,dataT29Column2Block2007,Block.length]

theorem checked537 : checkBlocks (fun n => n/512 ^^^ n%512) 240128 group537 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group538 : List Block := [dataT29Column2Block2008]

theorem length538 : (group538.map Block.length).sum = 512 := by
  simp [group538,dataT29Column2Block2008,Block.length]

theorem checked538 : checkBlocks (fun n => n/512 ^^^ n%512) 240640 group538 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group539 : List Block := [dataT29Column2Block2009]

theorem length539 : (group539.map Block.length).sum = 512 := by
  simp [group539,dataT29Column2Block2009,Block.length]

theorem checked539 : checkBlocks (fun n => n/512 ^^^ n%512) 241152 group539 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
