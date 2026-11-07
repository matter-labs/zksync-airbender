import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group56 : List Block := [dataT29Column2Block88]

theorem length56 : (group56.map Block.length).sum = 512 := by
  simp [group56,dataT29Column2Block88,Block.length]

theorem checked56 : checkBlocks (fun n => n/512 ^^^ n%512) 45056 group56 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group57 : List Block := [dataT29Column2Block89]

theorem length57 : (group57.map Block.length).sum = 512 := by
  simp [group57,dataT29Column2Block89,Block.length]

theorem checked57 : checkBlocks (fun n => n/512 ^^^ n%512) 45568 group57 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group58 : List Block := [dataT29Column2Block90]

theorem length58 : (group58.map Block.length).sum = 512 := by
  simp [group58,dataT29Column2Block90,Block.length]

theorem checked58 : checkBlocks (fun n => n/512 ^^^ n%512) 46080 group58 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group59 : List Block := [dataT29Column2Block91]

theorem length59 : (group59.map Block.length).sum = 512 := by
  simp [group59,dataT29Column2Block91,Block.length]

theorem checked59 : checkBlocks (fun n => n/512 ^^^ n%512) 46592 group59 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
