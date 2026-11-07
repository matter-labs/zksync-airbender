import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group364 : List Block := [dataT29Column2Block1361,dataT29Column2Block1362,dataT29Column2Block1363,dataT29Column2Block1364,dataT29Column2Block1365,dataT29Column2Block1366,dataT29Column2Block1367,dataT29Column2Block1368]

theorem length364 : (group364.map Block.length).sum = 128 := by
  simp [group364,dataT29Column2Block1361,dataT29Column2Block1362,dataT29Column2Block1363,dataT29Column2Block1364,dataT29Column2Block1365,dataT29Column2Block1366,dataT29Column2Block1367,dataT29Column2Block1368,Block.length]

theorem checked364 : checkBlocks (fun n => n/512 ^^^ n%512) 173312 group364 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group365 : List Block := [dataT29Column2Block1369,dataT29Column2Block1370,dataT29Column2Block1371,dataT29Column2Block1372,dataT29Column2Block1373,dataT29Column2Block1374,dataT29Column2Block1375,dataT29Column2Block1376]

theorem length365 : (group365.map Block.length).sum = 128 := by
  simp [group365,dataT29Column2Block1369,dataT29Column2Block1370,dataT29Column2Block1371,dataT29Column2Block1372,dataT29Column2Block1373,dataT29Column2Block1374,dataT29Column2Block1375,dataT29Column2Block1376,Block.length]

theorem checked365 : checkBlocks (fun n => n/512 ^^^ n%512) 173440 group365 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group366 : List Block := [dataT29Column2Block1377,dataT29Column2Block1378,dataT29Column2Block1379,dataT29Column2Block1380,dataT29Column2Block1381,dataT29Column2Block1382,dataT29Column2Block1383,dataT29Column2Block1384]

theorem length366 : (group366.map Block.length).sum = 128 := by
  simp [group366,dataT29Column2Block1377,dataT29Column2Block1378,dataT29Column2Block1379,dataT29Column2Block1380,dataT29Column2Block1381,dataT29Column2Block1382,dataT29Column2Block1383,dataT29Column2Block1384,Block.length]

theorem checked366 : checkBlocks (fun n => n/512 ^^^ n%512) 173568 group366 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group367 : List Block := [dataT29Column2Block1385,dataT29Column2Block1386,dataT29Column2Block1387,dataT29Column2Block1388,dataT29Column2Block1389,dataT29Column2Block1390,dataT29Column2Block1391,dataT29Column2Block1392]

theorem length367 : (group367.map Block.length).sum = 128 := by
  simp [group367,dataT29Column2Block1385,dataT29Column2Block1386,dataT29Column2Block1387,dataT29Column2Block1388,dataT29Column2Block1389,dataT29Column2Block1390,dataT29Column2Block1391,dataT29Column2Block1392,Block.length]

theorem checked367 : checkBlocks (fun n => n/512 ^^^ n%512) 173696 group367 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
