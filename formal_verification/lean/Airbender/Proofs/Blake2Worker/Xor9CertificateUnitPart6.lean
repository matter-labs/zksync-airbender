import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group24 : List Block := [dataT29Column2Block48,dataT29Column2Block49]

theorem length24 : (group24.map Block.length).sum = 1024 := by
  simp [group24,dataT29Column2Block48,dataT29Column2Block49,Block.length]

theorem checked24 : checkBlocks (fun n => n/512 ^^^ n%512) 24576 group24 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group25 : List Block := [dataT29Column2Block50,dataT29Column2Block51]

theorem length25 : (group25.map Block.length).sum = 1024 := by
  simp [group25,dataT29Column2Block50,dataT29Column2Block51,Block.length]

theorem checked25 : checkBlocks (fun n => n/512 ^^^ n%512) 25600 group25 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group26 : List Block := [dataT29Column2Block52,dataT29Column2Block53]

theorem length26 : (group26.map Block.length).sum = 1024 := by
  simp [group26,dataT29Column2Block52,dataT29Column2Block53,Block.length]

theorem checked26 : checkBlocks (fun n => n/512 ^^^ n%512) 26624 group26 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group27 : List Block := [dataT29Column2Block54,dataT29Column2Block55]

theorem length27 : (group27.map Block.length).sum = 1024 := by
  simp [group27,dataT29Column2Block54,dataT29Column2Block55,Block.length]

theorem checked27 : checkBlocks (fun n => n/512 ^^^ n%512) 27648 group27 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
