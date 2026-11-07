import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group100 : List Block := [dataT29Column2Block144,dataT29Column2Block145,dataT29Column2Block146,dataT29Column2Block147]

theorem length100 : (group100.map Block.length).sum = 512 := by
  simp [group100,dataT29Column2Block144,dataT29Column2Block145,dataT29Column2Block146,dataT29Column2Block147,Block.length]

theorem checked100 : checkBlocks (fun n => n/512 ^^^ n%512) 67584 group100 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group101 : List Block := [dataT29Column2Block148,dataT29Column2Block149,dataT29Column2Block150,dataT29Column2Block151]

theorem length101 : (group101.map Block.length).sum = 512 := by
  simp [group101,dataT29Column2Block148,dataT29Column2Block149,dataT29Column2Block150,dataT29Column2Block151,Block.length]

theorem checked101 : checkBlocks (fun n => n/512 ^^^ n%512) 68096 group101 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group102 : List Block := [dataT29Column2Block152,dataT29Column2Block153,dataT29Column2Block154,dataT29Column2Block155]

theorem length102 : (group102.map Block.length).sum = 512 := by
  simp [group102,dataT29Column2Block152,dataT29Column2Block153,dataT29Column2Block154,dataT29Column2Block155,Block.length]

theorem checked102 : checkBlocks (fun n => n/512 ^^^ n%512) 68608 group102 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group103 : List Block := [dataT29Column2Block156,dataT29Column2Block157,dataT29Column2Block158,dataT29Column2Block159]

theorem length103 : (group103.map Block.length).sum = 512 := by
  simp [group103,dataT29Column2Block156,dataT29Column2Block157,dataT29Column2Block158,dataT29Column2Block159,Block.length]

theorem checked103 : checkBlocks (fun n => n/512 ^^^ n%512) 69120 group103 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
