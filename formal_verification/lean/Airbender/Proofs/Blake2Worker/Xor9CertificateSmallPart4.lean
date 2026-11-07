import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group48 : List Block := [dataT29Column2Block80]

theorem length48 : (group48.map Block.length).sum = 512 := by
  simp [group48,dataT29Column2Block80,Block.length]

theorem checked48 : checkBlocks (fun n => n/512 ^^^ n%512) 40960 group48 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group49 : List Block := [dataT29Column2Block81]

theorem length49 : (group49.map Block.length).sum = 512 := by
  simp [group49,dataT29Column2Block81,Block.length]

theorem checked49 : checkBlocks (fun n => n/512 ^^^ n%512) 41472 group49 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group50 : List Block := [dataT29Column2Block82]

theorem length50 : (group50.map Block.length).sum = 512 := by
  simp [group50,dataT29Column2Block82,Block.length]

theorem checked50 : checkBlocks (fun n => n/512 ^^^ n%512) 41984 group50 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group51 : List Block := [dataT29Column2Block83]

theorem length51 : (group51.map Block.length).sum = 512 := by
  simp [group51,dataT29Column2Block83,Block.length]

theorem checked51 : checkBlocks (fun n => n/512 ^^^ n%512) 42496 group51 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
