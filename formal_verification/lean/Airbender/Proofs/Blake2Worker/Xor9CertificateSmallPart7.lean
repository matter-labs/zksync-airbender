import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group60 : List Block := [dataT29Column2Block92]

theorem length60 : (group60.map Block.length).sum = 512 := by
  simp [group60,dataT29Column2Block92,Block.length]

theorem checked60 : checkBlocks (fun n => n/512 ^^^ n%512) 47104 group60 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group61 : List Block := [dataT29Column2Block93]

theorem length61 : (group61.map Block.length).sum = 512 := by
  simp [group61,dataT29Column2Block93,Block.length]

theorem checked61 : checkBlocks (fun n => n/512 ^^^ n%512) 47616 group61 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group62 : List Block := [dataT29Column2Block94]

theorem length62 : (group62.map Block.length).sum = 512 := by
  simp [group62,dataT29Column2Block94,Block.length]

theorem checked62 : checkBlocks (fun n => n/512 ^^^ n%512) 48128 group62 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group63 : List Block := [dataT29Column2Block95]

theorem length63 : (group63.map Block.length).sum = 512 := by
  simp [group63,dataT29Column2Block95,Block.length]

theorem checked63 : checkBlocks (fun n => n/512 ^^^ n%512) 48640 group63 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
