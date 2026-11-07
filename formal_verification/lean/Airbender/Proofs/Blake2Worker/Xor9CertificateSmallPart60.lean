import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group272 : List Block := [dataT29Column2Block1022,dataT29Column2Block1023]

theorem length272 : (group272.map Block.length).sum = 512 := by
  simp [group272,dataT29Column2Block1022,dataT29Column2Block1023,Block.length]

theorem checked272 : checkBlocks (fun n => n/512 ^^^ n%512) 130304 group272 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group273 : List Block := [dataT29Column2Block1024]

theorem length273 : (group273.map Block.length).sum = 256 := by
  simp [group273,dataT29Column2Block1024,Block.length]

theorem checked273 : checkBlocks (fun n => n/512 ^^^ n%512) 130816 group273 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group274 : List Block := [dataT29Column2Block1025,dataT29Column2Block1026]

theorem length274 : (group274.map Block.length).sum = 512 := by
  simp [group274,dataT29Column2Block1025,dataT29Column2Block1026,Block.length]

theorem checked274 : checkBlocks (fun n => n/512 ^^^ n%512) 131072 group274 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group275 : List Block := [dataT29Column2Block1027,dataT29Column2Block1028]

theorem length275 : (group275.map Block.length).sum = 512 := by
  simp [group275,dataT29Column2Block1027,dataT29Column2Block1028,Block.length]

theorem checked275 : checkBlocks (fun n => n/512 ^^^ n%512) 131584 group275 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
