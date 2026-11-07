import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group336 : List Block := [dataT29Column2Block1149,dataT29Column2Block1150]

theorem length336 : (group336.map Block.length).sum = 512 := by
  simp [group336,dataT29Column2Block1149,dataT29Column2Block1150,Block.length]

theorem checked336 : checkBlocks (fun n => n/512 ^^^ n%512) 162816 group336 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group337 : List Block := [dataT29Column2Block1151,dataT29Column2Block1152]

theorem length337 : (group337.map Block.length).sum = 512 := by
  simp [group337,dataT29Column2Block1151,dataT29Column2Block1152,Block.length]

theorem checked337 : checkBlocks (fun n => n/512 ^^^ n%512) 163328 group337 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group338 : List Block := [dataT29Column2Block1153,dataT29Column2Block1154,dataT29Column2Block1155,dataT29Column2Block1156,dataT29Column2Block1157,dataT29Column2Block1158,dataT29Column2Block1159,dataT29Column2Block1160]

theorem length338 : (group338.map Block.length).sum = 512 := by
  simp [group338,dataT29Column2Block1153,dataT29Column2Block1154,dataT29Column2Block1155,dataT29Column2Block1156,dataT29Column2Block1157,dataT29Column2Block1158,dataT29Column2Block1159,dataT29Column2Block1160,Block.length]

theorem checked338 : checkBlocks (fun n => n/512 ^^^ n%512) 163840 group338 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group339 : List Block := [dataT29Column2Block1161,dataT29Column2Block1162,dataT29Column2Block1163,dataT29Column2Block1164,dataT29Column2Block1165,dataT29Column2Block1166,dataT29Column2Block1167,dataT29Column2Block1168]

theorem length339 : (group339.map Block.length).sum = 512 := by
  simp [group339,dataT29Column2Block1161,dataT29Column2Block1162,dataT29Column2Block1163,dataT29Column2Block1164,dataT29Column2Block1165,dataT29Column2Block1166,dataT29Column2Block1167,dataT29Column2Block1168,Block.length]

theorem checked339 : checkBlocks (fun n => n/512 ^^^ n%512) 164352 group339 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
