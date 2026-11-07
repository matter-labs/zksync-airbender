import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group108 : List Block := [dataT29Column2Block176,dataT29Column2Block177,dataT29Column2Block178,dataT29Column2Block179]

theorem length108 : (group108.map Block.length).sum = 512 := by
  simp [group108,dataT29Column2Block176,dataT29Column2Block177,dataT29Column2Block178,dataT29Column2Block179,Block.length]

theorem checked108 : checkBlocks (fun n => n/512 ^^^ n%512) 71680 group108 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group109 : List Block := [dataT29Column2Block180,dataT29Column2Block181,dataT29Column2Block182,dataT29Column2Block183]

theorem length109 : (group109.map Block.length).sum = 512 := by
  simp [group109,dataT29Column2Block180,dataT29Column2Block181,dataT29Column2Block182,dataT29Column2Block183,Block.length]

theorem checked109 : checkBlocks (fun n => n/512 ^^^ n%512) 72192 group109 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group110 : List Block := [dataT29Column2Block184,dataT29Column2Block185,dataT29Column2Block186,dataT29Column2Block187]

theorem length110 : (group110.map Block.length).sum = 512 := by
  simp [group110,dataT29Column2Block184,dataT29Column2Block185,dataT29Column2Block186,dataT29Column2Block187,Block.length]

theorem checked110 : checkBlocks (fun n => n/512 ^^^ n%512) 72704 group110 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group111 : List Block := [dataT29Column2Block188,dataT29Column2Block189,dataT29Column2Block190,dataT29Column2Block191]

theorem length111 : (group111.map Block.length).sum = 512 := by
  simp [group111,dataT29Column2Block188,dataT29Column2Block189,dataT29Column2Block190,dataT29Column2Block191,Block.length]

theorem checked111 : checkBlocks (fun n => n/512 ^^^ n%512) 73216 group111 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
