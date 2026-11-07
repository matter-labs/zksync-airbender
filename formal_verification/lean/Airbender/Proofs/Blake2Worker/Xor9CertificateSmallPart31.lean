import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group156 : List Block := [dataT29Column2Block480,dataT29Column2Block481,dataT29Column2Block482,dataT29Column2Block483,dataT29Column2Block484,dataT29Column2Block485,dataT29Column2Block486,dataT29Column2Block487]

theorem length156 : (group156.map Block.length).sum = 64 := by
  simp [group156,dataT29Column2Block480,dataT29Column2Block481,dataT29Column2Block482,dataT29Column2Block483,dataT29Column2Block484,dataT29Column2Block485,dataT29Column2Block486,dataT29Column2Block487,Block.length]

theorem checked156 : checkBlocks (fun n => n/512 ^^^ n%512) 86784 group156 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group157 : List Block := [dataT29Column2Block488,dataT29Column2Block489,dataT29Column2Block490,dataT29Column2Block491,dataT29Column2Block492,dataT29Column2Block493,dataT29Column2Block494,dataT29Column2Block495]

theorem length157 : (group157.map Block.length).sum = 64 := by
  simp [group157,dataT29Column2Block488,dataT29Column2Block489,dataT29Column2Block490,dataT29Column2Block491,dataT29Column2Block492,dataT29Column2Block493,dataT29Column2Block494,dataT29Column2Block495,Block.length]

theorem checked157 : checkBlocks (fun n => n/512 ^^^ n%512) 86848 group157 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group158 : List Block := [dataT29Column2Block496,dataT29Column2Block497,dataT29Column2Block498,dataT29Column2Block499,dataT29Column2Block500,dataT29Column2Block501,dataT29Column2Block502,dataT29Column2Block503]

theorem length158 : (group158.map Block.length).sum = 64 := by
  simp [group158,dataT29Column2Block496,dataT29Column2Block497,dataT29Column2Block498,dataT29Column2Block499,dataT29Column2Block500,dataT29Column2Block501,dataT29Column2Block502,dataT29Column2Block503,Block.length]

theorem checked158 : checkBlocks (fun n => n/512 ^^^ n%512) 86912 group158 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group159 : List Block := [dataT29Column2Block504,dataT29Column2Block505,dataT29Column2Block506,dataT29Column2Block507,dataT29Column2Block508,dataT29Column2Block509,dataT29Column2Block510,dataT29Column2Block511]

theorem length159 : (group159.map Block.length).sum = 64 := by
  simp [group159,dataT29Column2Block504,dataT29Column2Block505,dataT29Column2Block506,dataT29Column2Block507,dataT29Column2Block508,dataT29Column2Block509,dataT29Column2Block510,dataT29Column2Block511,Block.length]

theorem checked159 : checkBlocks (fun n => n/512 ^^^ n%512) 86976 group159 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
