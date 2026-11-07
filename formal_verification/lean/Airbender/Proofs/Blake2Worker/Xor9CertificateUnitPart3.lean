import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group12 : List Block := [dataT29Column2Block24,dataT29Column2Block25]

theorem length12 : (group12.map Block.length).sum = 1024 := by
  simp [group12,dataT29Column2Block24,dataT29Column2Block25,Block.length]

theorem checked12 : checkBlocks (fun n => n/512 ^^^ n%512) 12288 group12 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group13 : List Block := [dataT29Column2Block26,dataT29Column2Block27]

theorem length13 : (group13.map Block.length).sum = 1024 := by
  simp [group13,dataT29Column2Block26,dataT29Column2Block27,Block.length]

theorem checked13 : checkBlocks (fun n => n/512 ^^^ n%512) 13312 group13 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group14 : List Block := [dataT29Column2Block28,dataT29Column2Block29]

theorem length14 : (group14.map Block.length).sum = 1024 := by
  simp [group14,dataT29Column2Block28,dataT29Column2Block29,Block.length]

theorem checked14 : checkBlocks (fun n => n/512 ^^^ n%512) 14336 group14 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group15 : List Block := [dataT29Column2Block30,dataT29Column2Block31]

theorem length15 : (group15.map Block.length).sum = 1024 := by
  simp [group15,dataT29Column2Block30,dataT29Column2Block31,Block.length]

theorem checked15 : checkBlocks (fun n => n/512 ^^^ n%512) 15360 group15 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
