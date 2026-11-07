import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group352 : List Block := [dataT29Column2Block1265,dataT29Column2Block1266,dataT29Column2Block1267,dataT29Column2Block1268,dataT29Column2Block1269,dataT29Column2Block1270,dataT29Column2Block1271,dataT29Column2Block1272]

theorem length352 : (group352.map Block.length).sum = 512 := by
  simp [group352,dataT29Column2Block1265,dataT29Column2Block1266,dataT29Column2Block1267,dataT29Column2Block1268,dataT29Column2Block1269,dataT29Column2Block1270,dataT29Column2Block1271,dataT29Column2Block1272,Block.length]

theorem checked352 : checkBlocks (fun n => n/512 ^^^ n%512) 171008 group352 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group353 : List Block := [dataT29Column2Block1273,dataT29Column2Block1274,dataT29Column2Block1275,dataT29Column2Block1276,dataT29Column2Block1277,dataT29Column2Block1278,dataT29Column2Block1279,dataT29Column2Block1280]

theorem length353 : (group353.map Block.length).sum = 512 := by
  simp [group353,dataT29Column2Block1273,dataT29Column2Block1274,dataT29Column2Block1275,dataT29Column2Block1276,dataT29Column2Block1277,dataT29Column2Block1278,dataT29Column2Block1279,dataT29Column2Block1280,Block.length]

theorem checked353 : checkBlocks (fun n => n/512 ^^^ n%512) 171520 group353 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group354 : List Block := [dataT29Column2Block1281,dataT29Column2Block1282,dataT29Column2Block1283,dataT29Column2Block1284,dataT29Column2Block1285,dataT29Column2Block1286,dataT29Column2Block1287,dataT29Column2Block1288]

theorem length354 : (group354.map Block.length).sum = 128 := by
  simp [group354,dataT29Column2Block1281,dataT29Column2Block1282,dataT29Column2Block1283,dataT29Column2Block1284,dataT29Column2Block1285,dataT29Column2Block1286,dataT29Column2Block1287,dataT29Column2Block1288,Block.length]

theorem checked354 : checkBlocks (fun n => n/512 ^^^ n%512) 172032 group354 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group355 : List Block := [dataT29Column2Block1289,dataT29Column2Block1290,dataT29Column2Block1291,dataT29Column2Block1292,dataT29Column2Block1293,dataT29Column2Block1294,dataT29Column2Block1295,dataT29Column2Block1296]

theorem length355 : (group355.map Block.length).sum = 128 := by
  simp [group355,dataT29Column2Block1289,dataT29Column2Block1290,dataT29Column2Block1291,dataT29Column2Block1292,dataT29Column2Block1293,dataT29Column2Block1294,dataT29Column2Block1295,dataT29Column2Block1296,Block.length]

theorem checked355 : checkBlocks (fun n => n/512 ^^^ n%512) 172160 group355 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
