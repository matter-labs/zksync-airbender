import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group44 : List Block := [dataT29Column2Block76]

theorem length44 : (group44.map Block.length).sum = 512 := by
  simp [group44,dataT29Column2Block76,Block.length]

theorem checked44 : checkBlocks (fun n => n/512 ^^^ n%512) 38912 group44 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group45 : List Block := [dataT29Column2Block77]

theorem length45 : (group45.map Block.length).sum = 512 := by
  simp [group45,dataT29Column2Block77,Block.length]

theorem checked45 : checkBlocks (fun n => n/512 ^^^ n%512) 39424 group45 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group46 : List Block := [dataT29Column2Block78]

theorem length46 : (group46.map Block.length).sum = 512 := by
  simp [group46,dataT29Column2Block78,Block.length]

theorem checked46 : checkBlocks (fun n => n/512 ^^^ n%512) 39936 group46 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group47 : List Block := [dataT29Column2Block79]

theorem length47 : (group47.map Block.length).sum = 512 := by
  simp [group47,dataT29Column2Block79,Block.length]

theorem checked47 : checkBlocks (fun n => n/512 ^^^ n%512) 40448 group47 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
