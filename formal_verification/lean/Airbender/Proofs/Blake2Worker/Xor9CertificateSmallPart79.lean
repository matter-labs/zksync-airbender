import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group348 : List Block := [dataT29Column2Block1233,dataT29Column2Block1234,dataT29Column2Block1235,dataT29Column2Block1236,dataT29Column2Block1237,dataT29Column2Block1238,dataT29Column2Block1239,dataT29Column2Block1240]

theorem length348 : (group348.map Block.length).sum = 512 := by
  simp [group348,dataT29Column2Block1233,dataT29Column2Block1234,dataT29Column2Block1235,dataT29Column2Block1236,dataT29Column2Block1237,dataT29Column2Block1238,dataT29Column2Block1239,dataT29Column2Block1240,Block.length]

theorem checked348 : checkBlocks (fun n => n/512 ^^^ n%512) 168960 group348 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group349 : List Block := [dataT29Column2Block1241,dataT29Column2Block1242,dataT29Column2Block1243,dataT29Column2Block1244,dataT29Column2Block1245,dataT29Column2Block1246,dataT29Column2Block1247,dataT29Column2Block1248]

theorem length349 : (group349.map Block.length).sum = 512 := by
  simp [group349,dataT29Column2Block1241,dataT29Column2Block1242,dataT29Column2Block1243,dataT29Column2Block1244,dataT29Column2Block1245,dataT29Column2Block1246,dataT29Column2Block1247,dataT29Column2Block1248,Block.length]

theorem checked349 : checkBlocks (fun n => n/512 ^^^ n%512) 169472 group349 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group350 : List Block := [dataT29Column2Block1249,dataT29Column2Block1250,dataT29Column2Block1251,dataT29Column2Block1252,dataT29Column2Block1253,dataT29Column2Block1254,dataT29Column2Block1255,dataT29Column2Block1256]

theorem length350 : (group350.map Block.length).sum = 512 := by
  simp [group350,dataT29Column2Block1249,dataT29Column2Block1250,dataT29Column2Block1251,dataT29Column2Block1252,dataT29Column2Block1253,dataT29Column2Block1254,dataT29Column2Block1255,dataT29Column2Block1256,Block.length]

theorem checked350 : checkBlocks (fun n => n/512 ^^^ n%512) 169984 group350 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group351 : List Block := [dataT29Column2Block1257,dataT29Column2Block1258,dataT29Column2Block1259,dataT29Column2Block1260,dataT29Column2Block1261,dataT29Column2Block1262,dataT29Column2Block1263,dataT29Column2Block1264]

theorem length351 : (group351.map Block.length).sum = 512 := by
  simp [group351,dataT29Column2Block1257,dataT29Column2Block1258,dataT29Column2Block1259,dataT29Column2Block1260,dataT29Column2Block1261,dataT29Column2Block1262,dataT29Column2Block1263,dataT29Column2Block1264,Block.length]

theorem checked351 : checkBlocks (fun n => n/512 ^^^ n%512) 170496 group351 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
