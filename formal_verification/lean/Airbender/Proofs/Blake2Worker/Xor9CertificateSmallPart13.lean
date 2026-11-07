import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group84 : List Block := [dataT29Column2Block116]

theorem length84 : (group84.map Block.length).sum = 512 := by
  simp [group84,dataT29Column2Block116,Block.length]

theorem checked84 : checkBlocks (fun n => n/512 ^^^ n%512) 59392 group84 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group85 : List Block := [dataT29Column2Block117]

theorem length85 : (group85.map Block.length).sum = 512 := by
  simp [group85,dataT29Column2Block117,Block.length]

theorem checked85 : checkBlocks (fun n => n/512 ^^^ n%512) 59904 group85 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group86 : List Block := [dataT29Column2Block118]

theorem length86 : (group86.map Block.length).sum = 512 := by
  simp [group86,dataT29Column2Block118,Block.length]

theorem checked86 : checkBlocks (fun n => n/512 ^^^ n%512) 60416 group86 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group87 : List Block := [dataT29Column2Block119]

theorem length87 : (group87.map Block.length).sum = 512 := by
  simp [group87,dataT29Column2Block119,Block.length]

theorem checked87 : checkBlocks (fun n => n/512 ^^^ n%512) 60928 group87 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
