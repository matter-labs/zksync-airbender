import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group524 : List Block := [dataT29Column2Block1994]

theorem length524 : (group524.map Block.length).sum = 512 := by
  simp [group524,dataT29Column2Block1994,Block.length]

theorem checked524 : checkBlocks (fun n => n/512 ^^^ n%512) 233472 group524 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group525 : List Block := [dataT29Column2Block1995]

theorem length525 : (group525.map Block.length).sum = 512 := by
  simp [group525,dataT29Column2Block1995,Block.length]

theorem checked525 : checkBlocks (fun n => n/512 ^^^ n%512) 233984 group525 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group526 : List Block := [dataT29Column2Block1996]

theorem length526 : (group526.map Block.length).sum = 512 := by
  simp [group526,dataT29Column2Block1996,Block.length]

theorem checked526 : checkBlocks (fun n => n/512 ^^^ n%512) 234496 group526 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group527 : List Block := [dataT29Column2Block1997]

theorem length527 : (group527.map Block.length).sum = 512 := by
  simp [group527,dataT29Column2Block1997,Block.length]

theorem checked527 : checkBlocks (fun n => n/512 ^^^ n%512) 235008 group527 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
