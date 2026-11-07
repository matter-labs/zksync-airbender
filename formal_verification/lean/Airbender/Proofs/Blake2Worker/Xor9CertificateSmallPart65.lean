import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group292 : List Block := [dataT29Column2Block1061,dataT29Column2Block1062]

theorem length292 : (group292.map Block.length).sum = 512 := by
  simp [group292,dataT29Column2Block1061,dataT29Column2Block1062,Block.length]

theorem checked292 : checkBlocks (fun n => n/512 ^^^ n%512) 140288 group292 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group293 : List Block := [dataT29Column2Block1063,dataT29Column2Block1064]

theorem length293 : (group293.map Block.length).sum = 512 := by
  simp [group293,dataT29Column2Block1063,dataT29Column2Block1064,Block.length]

theorem checked293 : checkBlocks (fun n => n/512 ^^^ n%512) 140800 group293 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group294 : List Block := [dataT29Column2Block1065,dataT29Column2Block1066]

theorem length294 : (group294.map Block.length).sum = 512 := by
  simp [group294,dataT29Column2Block1065,dataT29Column2Block1066,Block.length]

theorem checked294 : checkBlocks (fun n => n/512 ^^^ n%512) 141312 group294 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group295 : List Block := [dataT29Column2Block1067,dataT29Column2Block1068]

theorem length295 : (group295.map Block.length).sum = 512 := by
  simp [group295,dataT29Column2Block1067,dataT29Column2Block1068,Block.length]

theorem checked295 : checkBlocks (fun n => n/512 ^^^ n%512) 141824 group295 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
