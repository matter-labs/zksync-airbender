import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group104 : List Block := [dataT29Column2Block160,dataT29Column2Block161,dataT29Column2Block162,dataT29Column2Block163]

theorem length104 : (group104.map Block.length).sum = 512 := by
  simp [group104,dataT29Column2Block160,dataT29Column2Block161,dataT29Column2Block162,dataT29Column2Block163,Block.length]

theorem checked104 : checkBlocks (fun n => n/512 ^^^ n%512) 69632 group104 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group105 : List Block := [dataT29Column2Block164,dataT29Column2Block165,dataT29Column2Block166,dataT29Column2Block167]

theorem length105 : (group105.map Block.length).sum = 512 := by
  simp [group105,dataT29Column2Block164,dataT29Column2Block165,dataT29Column2Block166,dataT29Column2Block167,Block.length]

theorem checked105 : checkBlocks (fun n => n/512 ^^^ n%512) 70144 group105 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group106 : List Block := [dataT29Column2Block168,dataT29Column2Block169,dataT29Column2Block170,dataT29Column2Block171]

theorem length106 : (group106.map Block.length).sum = 512 := by
  simp [group106,dataT29Column2Block168,dataT29Column2Block169,dataT29Column2Block170,dataT29Column2Block171,Block.length]

theorem checked106 : checkBlocks (fun n => n/512 ^^^ n%512) 70656 group106 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group107 : List Block := [dataT29Column2Block172,dataT29Column2Block173,dataT29Column2Block174,dataT29Column2Block175]

theorem length107 : (group107.map Block.length).sum = 512 := by
  simp [group107,dataT29Column2Block172,dataT29Column2Block173,dataT29Column2Block174,dataT29Column2Block175,Block.length]

theorem checked107 : checkBlocks (fun n => n/512 ^^^ n%512) 71168 group107 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
