import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group76 : List Block := [dataT29Column2Block108]

theorem length76 : (group76.map Block.length).sum = 512 := by
  simp [group76,dataT29Column2Block108,Block.length]

theorem checked76 : checkBlocks (fun n => n/512 ^^^ n%512) 55296 group76 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group77 : List Block := [dataT29Column2Block109]

theorem length77 : (group77.map Block.length).sum = 512 := by
  simp [group77,dataT29Column2Block109,Block.length]

theorem checked77 : checkBlocks (fun n => n/512 ^^^ n%512) 55808 group77 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group78 : List Block := [dataT29Column2Block110]

theorem length78 : (group78.map Block.length).sum = 512 := by
  simp [group78,dataT29Column2Block110,Block.length]

theorem checked78 : checkBlocks (fun n => n/512 ^^^ n%512) 56320 group78 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group79 : List Block := [dataT29Column2Block111]

theorem length79 : (group79.map Block.length).sum = 512 := by
  simp [group79,dataT29Column2Block111,Block.length]

theorem checked79 : checkBlocks (fun n => n/512 ^^^ n%512) 56832 group79 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
