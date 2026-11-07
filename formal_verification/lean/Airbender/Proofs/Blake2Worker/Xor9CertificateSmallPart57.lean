import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group260 : List Block := [dataT29Column2Block998,dataT29Column2Block999]

theorem length260 : (group260.map Block.length).sum = 512 := by
  simp [group260,dataT29Column2Block998,dataT29Column2Block999,Block.length]

theorem checked260 : checkBlocks (fun n => n/512 ^^^ n%512) 124160 group260 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group261 : List Block := [dataT29Column2Block1000,dataT29Column2Block1001]

theorem length261 : (group261.map Block.length).sum = 512 := by
  simp [group261,dataT29Column2Block1000,dataT29Column2Block1001,Block.length]

theorem checked261 : checkBlocks (fun n => n/512 ^^^ n%512) 124672 group261 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group262 : List Block := [dataT29Column2Block1002,dataT29Column2Block1003]

theorem length262 : (group262.map Block.length).sum = 512 := by
  simp [group262,dataT29Column2Block1002,dataT29Column2Block1003,Block.length]

theorem checked262 : checkBlocks (fun n => n/512 ^^^ n%512) 125184 group262 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group263 : List Block := [dataT29Column2Block1004,dataT29Column2Block1005]

theorem length263 : (group263.map Block.length).sum = 512 := by
  simp [group263,dataT29Column2Block1004,dataT29Column2Block1005,Block.length]

theorem checked263 : checkBlocks (fun n => n/512 ^^^ n%512) 125696 group263 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
