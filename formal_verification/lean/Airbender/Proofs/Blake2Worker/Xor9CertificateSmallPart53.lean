import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group244 : List Block := [dataT29Column2Block966,dataT29Column2Block967]

theorem length244 : (group244.map Block.length).sum = 512 := by
  simp [group244,dataT29Column2Block966,dataT29Column2Block967,Block.length]

theorem checked244 : checkBlocks (fun n => n/512 ^^^ n%512) 115968 group244 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group245 : List Block := [dataT29Column2Block968,dataT29Column2Block969]

theorem length245 : (group245.map Block.length).sum = 512 := by
  simp [group245,dataT29Column2Block968,dataT29Column2Block969,Block.length]

theorem checked245 : checkBlocks (fun n => n/512 ^^^ n%512) 116480 group245 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group246 : List Block := [dataT29Column2Block970,dataT29Column2Block971]

theorem length246 : (group246.map Block.length).sum = 512 := by
  simp [group246,dataT29Column2Block970,dataT29Column2Block971,Block.length]

theorem checked246 : checkBlocks (fun n => n/512 ^^^ n%512) 116992 group246 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group247 : List Block := [dataT29Column2Block972,dataT29Column2Block973]

theorem length247 : (group247.map Block.length).sum = 512 := by
  simp [group247,dataT29Column2Block972,dataT29Column2Block973,Block.length]

theorem checked247 : checkBlocks (fun n => n/512 ^^^ n%512) 117504 group247 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
