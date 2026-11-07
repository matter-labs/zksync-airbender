import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group268 : List Block := [dataT29Column2Block1014,dataT29Column2Block1015]

theorem length268 : (group268.map Block.length).sum = 512 := by
  simp [group268,dataT29Column2Block1014,dataT29Column2Block1015,Block.length]

theorem checked268 : checkBlocks (fun n => n/512 ^^^ n%512) 128256 group268 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group269 : List Block := [dataT29Column2Block1016,dataT29Column2Block1017]

theorem length269 : (group269.map Block.length).sum = 512 := by
  simp [group269,dataT29Column2Block1016,dataT29Column2Block1017,Block.length]

theorem checked269 : checkBlocks (fun n => n/512 ^^^ n%512) 128768 group269 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group270 : List Block := [dataT29Column2Block1018,dataT29Column2Block1019]

theorem length270 : (group270.map Block.length).sum = 512 := by
  simp [group270,dataT29Column2Block1018,dataT29Column2Block1019,Block.length]

theorem checked270 : checkBlocks (fun n => n/512 ^^^ n%512) 129280 group270 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group271 : List Block := [dataT29Column2Block1020,dataT29Column2Block1021]

theorem length271 : (group271.map Block.length).sum = 512 := by
  simp [group271,dataT29Column2Block1020,dataT29Column2Block1021,Block.length]

theorem checked271 : checkBlocks (fun n => n/512 ^^^ n%512) 129792 group271 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
