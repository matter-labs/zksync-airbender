import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group532 : List Block := [dataT29Column2Block2002]

theorem length532 : (group532.map Block.length).sum = 512 := by
  simp [group532,dataT29Column2Block2002,Block.length]

theorem checked532 : checkBlocks (fun n => n/512 ^^^ n%512) 237568 group532 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group533 : List Block := [dataT29Column2Block2003]

theorem length533 : (group533.map Block.length).sum = 512 := by
  simp [group533,dataT29Column2Block2003,Block.length]

theorem checked533 : checkBlocks (fun n => n/512 ^^^ n%512) 238080 group533 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group534 : List Block := [dataT29Column2Block2004]

theorem length534 : (group534.map Block.length).sum = 512 := by
  simp [group534,dataT29Column2Block2004,Block.length]

theorem checked534 : checkBlocks (fun n => n/512 ^^^ n%512) 238592 group534 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group535 : List Block := [dataT29Column2Block2005]

theorem length535 : (group535.map Block.length).sum = 512 := by
  simp [group535,dataT29Column2Block2005,Block.length]

theorem checked535 : checkBlocks (fun n => n/512 ^^^ n%512) 239104 group535 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
