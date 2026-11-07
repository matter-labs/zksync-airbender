import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group40 : List Block := [dataT29Column2Block72]

theorem length40 : (group40.map Block.length).sum = 512 := by
  simp [group40,dataT29Column2Block72,Block.length]

theorem checked40 : checkBlocks (fun n => n/512 ^^^ n%512) 36864 group40 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group41 : List Block := [dataT29Column2Block73]

theorem length41 : (group41.map Block.length).sum = 512 := by
  simp [group41,dataT29Column2Block73,Block.length]

theorem checked41 : checkBlocks (fun n => n/512 ^^^ n%512) 37376 group41 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group42 : List Block := [dataT29Column2Block74]

theorem length42 : (group42.map Block.length).sum = 512 := by
  simp [group42,dataT29Column2Block74,Block.length]

theorem checked42 : checkBlocks (fun n => n/512 ^^^ n%512) 37888 group42 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group43 : List Block := [dataT29Column2Block75]

theorem length43 : (group43.map Block.length).sum = 512 := by
  simp [group43,dataT29Column2Block75,Block.length]

theorem checked43 : checkBlocks (fun n => n/512 ^^^ n%512) 38400 group43 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
