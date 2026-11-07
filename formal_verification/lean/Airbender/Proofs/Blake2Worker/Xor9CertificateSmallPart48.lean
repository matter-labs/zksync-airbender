import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group224 : List Block := [dataT29Column2Block926,dataT29Column2Block927]

theorem length224 : (group224.map Block.length).sum = 512 := by
  simp [group224,dataT29Column2Block926,dataT29Column2Block927,Block.length]

theorem checked224 : checkBlocks (fun n => n/512 ^^^ n%512) 105728 group224 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group225 : List Block := [dataT29Column2Block928,dataT29Column2Block929]

theorem length225 : (group225.map Block.length).sum = 512 := by
  simp [group225,dataT29Column2Block928,dataT29Column2Block929,Block.length]

theorem checked225 : checkBlocks (fun n => n/512 ^^^ n%512) 106240 group225 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group226 : List Block := [dataT29Column2Block930,dataT29Column2Block931]

theorem length226 : (group226.map Block.length).sum = 512 := by
  simp [group226,dataT29Column2Block930,dataT29Column2Block931,Block.length]

theorem checked226 : checkBlocks (fun n => n/512 ^^^ n%512) 106752 group226 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group227 : List Block := [dataT29Column2Block932,dataT29Column2Block933]

theorem length227 : (group227.map Block.length).sum = 512 := by
  simp [group227,dataT29Column2Block932,dataT29Column2Block933,Block.length]

theorem checked227 : checkBlocks (fun n => n/512 ^^^ n%512) 107264 group227 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
