import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group288 : List Block := [dataT29Column2Block1053,dataT29Column2Block1054]

theorem length288 : (group288.map Block.length).sum = 512 := by
  simp [group288,dataT29Column2Block1053,dataT29Column2Block1054,Block.length]

theorem checked288 : checkBlocks (fun n => n/512 ^^^ n%512) 138240 group288 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group289 : List Block := [dataT29Column2Block1055,dataT29Column2Block1056]

theorem length289 : (group289.map Block.length).sum = 512 := by
  simp [group289,dataT29Column2Block1055,dataT29Column2Block1056,Block.length]

theorem checked289 : checkBlocks (fun n => n/512 ^^^ n%512) 138752 group289 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group290 : List Block := [dataT29Column2Block1057,dataT29Column2Block1058]

theorem length290 : (group290.map Block.length).sum = 512 := by
  simp [group290,dataT29Column2Block1057,dataT29Column2Block1058,Block.length]

theorem checked290 : checkBlocks (fun n => n/512 ^^^ n%512) 139264 group290 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group291 : List Block := [dataT29Column2Block1059,dataT29Column2Block1060]

theorem length291 : (group291.map Block.length).sum = 512 := by
  simp [group291,dataT29Column2Block1059,dataT29Column2Block1060,Block.length]

theorem checked291 : checkBlocks (fun n => n/512 ^^^ n%512) 139776 group291 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
