import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group552 : List Block := [dataT29Column2Block2022]

theorem length552 : (group552.map Block.length).sum = 512 := by
  simp [group552,dataT29Column2Block2022,Block.length]

theorem checked552 : checkBlocks (fun n => n/512 ^^^ n%512) 247808 group552 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group553 : List Block := [dataT29Column2Block2023]

theorem length553 : (group553.map Block.length).sum = 512 := by
  simp [group553,dataT29Column2Block2023,Block.length]

theorem checked553 : checkBlocks (fun n => n/512 ^^^ n%512) 248320 group553 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group554 : List Block := [dataT29Column2Block2024]

theorem length554 : (group554.map Block.length).sum = 512 := by
  simp [group554,dataT29Column2Block2024,Block.length]

theorem checked554 : checkBlocks (fun n => n/512 ^^^ n%512) 248832 group554 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group555 : List Block := [dataT29Column2Block2025]

theorem length555 : (group555.map Block.length).sum = 512 := by
  simp [group555,dataT29Column2Block2025,Block.length]

theorem checked555 : checkBlocks (fun n => n/512 ^^^ n%512) 249344 group555 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
