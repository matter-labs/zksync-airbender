import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group248 : List Block := [dataT29Column2Block974,dataT29Column2Block975]

theorem length248 : (group248.map Block.length).sum = 512 := by
  simp [group248,dataT29Column2Block974,dataT29Column2Block975,Block.length]

theorem checked248 : checkBlocks (fun n => n/512 ^^^ n%512) 118016 group248 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group249 : List Block := [dataT29Column2Block976,dataT29Column2Block977]

theorem length249 : (group249.map Block.length).sum = 512 := by
  simp [group249,dataT29Column2Block976,dataT29Column2Block977,Block.length]

theorem checked249 : checkBlocks (fun n => n/512 ^^^ n%512) 118528 group249 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group250 : List Block := [dataT29Column2Block978,dataT29Column2Block979]

theorem length250 : (group250.map Block.length).sum = 512 := by
  simp [group250,dataT29Column2Block978,dataT29Column2Block979,Block.length]

theorem checked250 : checkBlocks (fun n => n/512 ^^^ n%512) 119040 group250 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group251 : List Block := [dataT29Column2Block980,dataT29Column2Block981]

theorem length251 : (group251.map Block.length).sum = 512 := by
  simp [group251,dataT29Column2Block980,dataT29Column2Block981,Block.length]

theorem checked251 : checkBlocks (fun n => n/512 ^^^ n%512) 119552 group251 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
