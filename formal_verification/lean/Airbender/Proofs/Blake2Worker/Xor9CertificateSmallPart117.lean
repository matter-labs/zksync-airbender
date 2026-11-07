import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group500 : List Block := [dataT29Column2Block1970]

theorem length500 : (group500.map Block.length).sum = 512 := by
  simp [group500,dataT29Column2Block1970,Block.length]

theorem checked500 : checkBlocks (fun n => n/512 ^^^ n%512) 221184 group500 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group501 : List Block := [dataT29Column2Block1971]

theorem length501 : (group501.map Block.length).sum = 512 := by
  simp [group501,dataT29Column2Block1971,Block.length]

theorem checked501 : checkBlocks (fun n => n/512 ^^^ n%512) 221696 group501 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group502 : List Block := [dataT29Column2Block1972]

theorem length502 : (group502.map Block.length).sum = 512 := by
  simp [group502,dataT29Column2Block1972,Block.length]

theorem checked502 : checkBlocks (fun n => n/512 ^^^ n%512) 222208 group502 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group503 : List Block := [dataT29Column2Block1973]

theorem length503 : (group503.map Block.length).sum = 512 := by
  simp [group503,dataT29Column2Block1973,Block.length]

theorem checked503 : checkBlocks (fun n => n/512 ^^^ n%512) 222720 group503 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
