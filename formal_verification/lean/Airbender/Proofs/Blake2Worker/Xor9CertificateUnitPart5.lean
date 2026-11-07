import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group20 : List Block := [dataT29Column2Block40,dataT29Column2Block41]

theorem length20 : (group20.map Block.length).sum = 1024 := by
  simp [group20,dataT29Column2Block40,dataT29Column2Block41,Block.length]

theorem checked20 : checkBlocks (fun n => n/512 ^^^ n%512) 20480 group20 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group21 : List Block := [dataT29Column2Block42,dataT29Column2Block43]

theorem length21 : (group21.map Block.length).sum = 1024 := by
  simp [group21,dataT29Column2Block42,dataT29Column2Block43,Block.length]

theorem checked21 : checkBlocks (fun n => n/512 ^^^ n%512) 21504 group21 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group22 : List Block := [dataT29Column2Block44,dataT29Column2Block45]

theorem length22 : (group22.map Block.length).sum = 1024 := by
  simp [group22,dataT29Column2Block44,dataT29Column2Block45,Block.length]

theorem checked22 : checkBlocks (fun n => n/512 ^^^ n%512) 22528 group22 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group23 : List Block := [dataT29Column2Block46,dataT29Column2Block47]

theorem length23 : (group23.map Block.length).sum = 1024 := by
  simp [group23,dataT29Column2Block46,dataT29Column2Block47,Block.length]

theorem checked23 : checkBlocks (fun n => n/512 ^^^ n%512) 23552 group23 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
