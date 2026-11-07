import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group340 : List Block := [dataT29Column2Block1169,dataT29Column2Block1170,dataT29Column2Block1171,dataT29Column2Block1172,dataT29Column2Block1173,dataT29Column2Block1174,dataT29Column2Block1175,dataT29Column2Block1176]

theorem length340 : (group340.map Block.length).sum = 512 := by
  simp [group340,dataT29Column2Block1169,dataT29Column2Block1170,dataT29Column2Block1171,dataT29Column2Block1172,dataT29Column2Block1173,dataT29Column2Block1174,dataT29Column2Block1175,dataT29Column2Block1176,Block.length]

theorem checked340 : checkBlocks (fun n => n/512 ^^^ n%512) 164864 group340 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group341 : List Block := [dataT29Column2Block1177,dataT29Column2Block1178,dataT29Column2Block1179,dataT29Column2Block1180,dataT29Column2Block1181,dataT29Column2Block1182,dataT29Column2Block1183,dataT29Column2Block1184]

theorem length341 : (group341.map Block.length).sum = 512 := by
  simp [group341,dataT29Column2Block1177,dataT29Column2Block1178,dataT29Column2Block1179,dataT29Column2Block1180,dataT29Column2Block1181,dataT29Column2Block1182,dataT29Column2Block1183,dataT29Column2Block1184,Block.length]

theorem checked341 : checkBlocks (fun n => n/512 ^^^ n%512) 165376 group341 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group342 : List Block := [dataT29Column2Block1185,dataT29Column2Block1186,dataT29Column2Block1187,dataT29Column2Block1188,dataT29Column2Block1189,dataT29Column2Block1190,dataT29Column2Block1191,dataT29Column2Block1192]

theorem length342 : (group342.map Block.length).sum = 512 := by
  simp [group342,dataT29Column2Block1185,dataT29Column2Block1186,dataT29Column2Block1187,dataT29Column2Block1188,dataT29Column2Block1189,dataT29Column2Block1190,dataT29Column2Block1191,dataT29Column2Block1192,Block.length]

theorem checked342 : checkBlocks (fun n => n/512 ^^^ n%512) 165888 group342 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group343 : List Block := [dataT29Column2Block1193,dataT29Column2Block1194,dataT29Column2Block1195,dataT29Column2Block1196,dataT29Column2Block1197,dataT29Column2Block1198,dataT29Column2Block1199,dataT29Column2Block1200]

theorem length343 : (group343.map Block.length).sum = 512 := by
  simp [group343,dataT29Column2Block1193,dataT29Column2Block1194,dataT29Column2Block1195,dataT29Column2Block1196,dataT29Column2Block1197,dataT29Column2Block1198,dataT29Column2Block1199,dataT29Column2Block1200,Block.length]

theorem checked343 : checkBlocks (fun n => n/512 ^^^ n%512) 166400 group343 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
