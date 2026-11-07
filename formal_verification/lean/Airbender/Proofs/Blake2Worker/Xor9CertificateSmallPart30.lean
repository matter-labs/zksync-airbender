import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group152 : List Block := [dataT29Column2Block448,dataT29Column2Block449,dataT29Column2Block450,dataT29Column2Block451,dataT29Column2Block452,dataT29Column2Block453,dataT29Column2Block454,dataT29Column2Block455]

theorem length152 : (group152.map Block.length).sum = 64 := by
  simp [group152,dataT29Column2Block448,dataT29Column2Block449,dataT29Column2Block450,dataT29Column2Block451,dataT29Column2Block452,dataT29Column2Block453,dataT29Column2Block454,dataT29Column2Block455,Block.length]

theorem checked152 : checkBlocks (fun n => n/512 ^^^ n%512) 86528 group152 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group153 : List Block := [dataT29Column2Block456,dataT29Column2Block457,dataT29Column2Block458,dataT29Column2Block459,dataT29Column2Block460,dataT29Column2Block461,dataT29Column2Block462,dataT29Column2Block463]

theorem length153 : (group153.map Block.length).sum = 64 := by
  simp [group153,dataT29Column2Block456,dataT29Column2Block457,dataT29Column2Block458,dataT29Column2Block459,dataT29Column2Block460,dataT29Column2Block461,dataT29Column2Block462,dataT29Column2Block463,Block.length]

theorem checked153 : checkBlocks (fun n => n/512 ^^^ n%512) 86592 group153 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group154 : List Block := [dataT29Column2Block464,dataT29Column2Block465,dataT29Column2Block466,dataT29Column2Block467,dataT29Column2Block468,dataT29Column2Block469,dataT29Column2Block470,dataT29Column2Block471]

theorem length154 : (group154.map Block.length).sum = 64 := by
  simp [group154,dataT29Column2Block464,dataT29Column2Block465,dataT29Column2Block466,dataT29Column2Block467,dataT29Column2Block468,dataT29Column2Block469,dataT29Column2Block470,dataT29Column2Block471,Block.length]

theorem checked154 : checkBlocks (fun n => n/512 ^^^ n%512) 86656 group154 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group155 : List Block := [dataT29Column2Block472,dataT29Column2Block473,dataT29Column2Block474,dataT29Column2Block475,dataT29Column2Block476,dataT29Column2Block477,dataT29Column2Block478,dataT29Column2Block479]

theorem length155 : (group155.map Block.length).sum = 64 := by
  simp [group155,dataT29Column2Block472,dataT29Column2Block473,dataT29Column2Block474,dataT29Column2Block475,dataT29Column2Block476,dataT29Column2Block477,dataT29Column2Block478,dataT29Column2Block479,Block.length]

theorem checked155 : checkBlocks (fun n => n/512 ^^^ n%512) 86720 group155 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
