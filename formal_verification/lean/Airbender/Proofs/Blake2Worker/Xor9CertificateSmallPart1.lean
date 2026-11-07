import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group36 : List Block := [dataT29Column2Block68]

theorem length36 : (group36.map Block.length).sum = 512 := by
  simp [group36,dataT29Column2Block68,Block.length]

theorem checked36 : checkBlocks (fun n => n/512 ^^^ n%512) 34816 group36 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group37 : List Block := [dataT29Column2Block69]

theorem length37 : (group37.map Block.length).sum = 512 := by
  simp [group37,dataT29Column2Block69,Block.length]

theorem checked37 : checkBlocks (fun n => n/512 ^^^ n%512) 35328 group37 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group38 : List Block := [dataT29Column2Block70]

theorem length38 : (group38.map Block.length).sum = 512 := by
  simp [group38,dataT29Column2Block70,Block.length]

theorem checked38 : checkBlocks (fun n => n/512 ^^^ n%512) 35840 group38 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group39 : List Block := [dataT29Column2Block71]

theorem length39 : (group39.map Block.length).sum = 512 := by
  simp [group39,dataT29Column2Block71,Block.length]

theorem checked39 : checkBlocks (fun n => n/512 ^^^ n%512) 36352 group39 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
