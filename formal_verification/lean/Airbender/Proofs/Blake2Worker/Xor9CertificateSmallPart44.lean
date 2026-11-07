import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group208 : List Block := [dataT29Column2Block888,dataT29Column2Block889,dataT29Column2Block890,dataT29Column2Block891,dataT29Column2Block892,dataT29Column2Block893,dataT29Column2Block894,dataT29Column2Block895]

theorem length208 : (group208.map Block.length).sum = 512 := by
  simp [group208,dataT29Column2Block888,dataT29Column2Block889,dataT29Column2Block890,dataT29Column2Block891,dataT29Column2Block892,dataT29Column2Block893,dataT29Column2Block894,dataT29Column2Block895,Block.length]

theorem checked208 : checkBlocks (fun n => n/512 ^^^ n%512) 97728 group208 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group209 : List Block := [dataT29Column2Block896,dataT29Column2Block897]

theorem length209 : (group209.map Block.length).sum = 320 := by
  simp [group209,dataT29Column2Block896,dataT29Column2Block897,Block.length]

theorem checked209 : checkBlocks (fun n => n/512 ^^^ n%512) 98240 group209 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group210 : List Block := [dataT29Column2Block898,dataT29Column2Block899]

theorem length210 : (group210.map Block.length).sum = 512 := by
  simp [group210,dataT29Column2Block898,dataT29Column2Block899,Block.length]

theorem checked210 : checkBlocks (fun n => n/512 ^^^ n%512) 98560 group210 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group211 : List Block := [dataT29Column2Block900,dataT29Column2Block901]

theorem length211 : (group211.map Block.length).sum = 512 := by
  simp [group211,dataT29Column2Block900,dataT29Column2Block901,Block.length]

theorem checked211 : checkBlocks (fun n => n/512 ^^^ n%512) 99072 group211 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
