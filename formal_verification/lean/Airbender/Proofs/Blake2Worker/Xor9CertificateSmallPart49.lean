import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group228 : List Block := [dataT29Column2Block934,dataT29Column2Block935]

theorem length228 : (group228.map Block.length).sum = 512 := by
  simp [group228,dataT29Column2Block934,dataT29Column2Block935,Block.length]

theorem checked228 : checkBlocks (fun n => n/512 ^^^ n%512) 107776 group228 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group229 : List Block := [dataT29Column2Block936,dataT29Column2Block937]

theorem length229 : (group229.map Block.length).sum = 512 := by
  simp [group229,dataT29Column2Block936,dataT29Column2Block937,Block.length]

theorem checked229 : checkBlocks (fun n => n/512 ^^^ n%512) 108288 group229 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group230 : List Block := [dataT29Column2Block938,dataT29Column2Block939]

theorem length230 : (group230.map Block.length).sum = 512 := by
  simp [group230,dataT29Column2Block938,dataT29Column2Block939,Block.length]

theorem checked230 : checkBlocks (fun n => n/512 ^^^ n%512) 108800 group230 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group231 : List Block := [dataT29Column2Block940,dataT29Column2Block941]

theorem length231 : (group231.map Block.length).sum = 512 := by
  simp [group231,dataT29Column2Block940,dataT29Column2Block941,Block.length]

theorem checked231 : checkBlocks (fun n => n/512 ^^^ n%512) 109312 group231 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
