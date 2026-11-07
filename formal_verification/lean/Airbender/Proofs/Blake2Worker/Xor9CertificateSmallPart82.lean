import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group360 : List Block := [dataT29Column2Block1329,dataT29Column2Block1330,dataT29Column2Block1331,dataT29Column2Block1332,dataT29Column2Block1333,dataT29Column2Block1334,dataT29Column2Block1335,dataT29Column2Block1336]

theorem length360 : (group360.map Block.length).sum = 128 := by
  simp [group360,dataT29Column2Block1329,dataT29Column2Block1330,dataT29Column2Block1331,dataT29Column2Block1332,dataT29Column2Block1333,dataT29Column2Block1334,dataT29Column2Block1335,dataT29Column2Block1336,Block.length]

theorem checked360 : checkBlocks (fun n => n/512 ^^^ n%512) 172800 group360 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group361 : List Block := [dataT29Column2Block1337,dataT29Column2Block1338,dataT29Column2Block1339,dataT29Column2Block1340,dataT29Column2Block1341,dataT29Column2Block1342,dataT29Column2Block1343,dataT29Column2Block1344]

theorem length361 : (group361.map Block.length).sum = 128 := by
  simp [group361,dataT29Column2Block1337,dataT29Column2Block1338,dataT29Column2Block1339,dataT29Column2Block1340,dataT29Column2Block1341,dataT29Column2Block1342,dataT29Column2Block1343,dataT29Column2Block1344,Block.length]

theorem checked361 : checkBlocks (fun n => n/512 ^^^ n%512) 172928 group361 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group362 : List Block := [dataT29Column2Block1345,dataT29Column2Block1346,dataT29Column2Block1347,dataT29Column2Block1348,dataT29Column2Block1349,dataT29Column2Block1350,dataT29Column2Block1351,dataT29Column2Block1352]

theorem length362 : (group362.map Block.length).sum = 128 := by
  simp [group362,dataT29Column2Block1345,dataT29Column2Block1346,dataT29Column2Block1347,dataT29Column2Block1348,dataT29Column2Block1349,dataT29Column2Block1350,dataT29Column2Block1351,dataT29Column2Block1352,Block.length]

theorem checked362 : checkBlocks (fun n => n/512 ^^^ n%512) 173056 group362 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group363 : List Block := [dataT29Column2Block1353,dataT29Column2Block1354,dataT29Column2Block1355,dataT29Column2Block1356,dataT29Column2Block1357,dataT29Column2Block1358,dataT29Column2Block1359,dataT29Column2Block1360]

theorem length363 : (group363.map Block.length).sum = 128 := by
  simp [group363,dataT29Column2Block1353,dataT29Column2Block1354,dataT29Column2Block1355,dataT29Column2Block1356,dataT29Column2Block1357,dataT29Column2Block1358,dataT29Column2Block1359,dataT29Column2Block1360,Block.length]

theorem checked363 : checkBlocks (fun n => n/512 ^^^ n%512) 173184 group363 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
