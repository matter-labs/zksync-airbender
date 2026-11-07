import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group72 : List Block := [dataT29Column2Block104]

theorem length72 : (group72.map Block.length).sum = 512 := by
  simp [group72,dataT29Column2Block104,Block.length]

theorem checked72 : checkBlocks (fun n => n/512 ^^^ n%512) 53248 group72 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group73 : List Block := [dataT29Column2Block105]

theorem length73 : (group73.map Block.length).sum = 512 := by
  simp [group73,dataT29Column2Block105,Block.length]

theorem checked73 : checkBlocks (fun n => n/512 ^^^ n%512) 53760 group73 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group74 : List Block := [dataT29Column2Block106]

theorem length74 : (group74.map Block.length).sum = 512 := by
  simp [group74,dataT29Column2Block106,Block.length]

theorem checked74 : checkBlocks (fun n => n/512 ^^^ n%512) 54272 group74 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group75 : List Block := [dataT29Column2Block107]

theorem length75 : (group75.map Block.length).sum = 512 := by
  simp [group75,dataT29Column2Block107,Block.length]

theorem checked75 : checkBlocks (fun n => n/512 ^^^ n%512) 54784 group75 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
