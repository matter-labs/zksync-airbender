import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group544 : List Block := [dataT29Column2Block2014]

theorem length544 : (group544.map Block.length).sum = 512 := by
  simp [group544,dataT29Column2Block2014,Block.length]

theorem checked544 : checkBlocks (fun n => n/512 ^^^ n%512) 243712 group544 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group545 : List Block := [dataT29Column2Block2015]

theorem length545 : (group545.map Block.length).sum = 512 := by
  simp [group545,dataT29Column2Block2015,Block.length]

theorem checked545 : checkBlocks (fun n => n/512 ^^^ n%512) 244224 group545 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group546 : List Block := [dataT29Column2Block2016]

theorem length546 : (group546.map Block.length).sum = 512 := by
  simp [group546,dataT29Column2Block2016,Block.length]

theorem checked546 : checkBlocks (fun n => n/512 ^^^ n%512) 244736 group546 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group547 : List Block := [dataT29Column2Block2017]

theorem length547 : (group547.map Block.length).sum = 512 := by
  simp [group547,dataT29Column2Block2017,Block.length]

theorem checked547 : checkBlocks (fun n => n/512 ^^^ n%512) 245248 group547 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
