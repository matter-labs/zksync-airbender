import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group356 : List Block := [dataT29Column2Block1297,dataT29Column2Block1298,dataT29Column2Block1299,dataT29Column2Block1300,dataT29Column2Block1301,dataT29Column2Block1302,dataT29Column2Block1303,dataT29Column2Block1304]

theorem length356 : (group356.map Block.length).sum = 128 := by
  simp [group356,dataT29Column2Block1297,dataT29Column2Block1298,dataT29Column2Block1299,dataT29Column2Block1300,dataT29Column2Block1301,dataT29Column2Block1302,dataT29Column2Block1303,dataT29Column2Block1304,Block.length]

theorem checked356 : checkBlocks (fun n => n/512 ^^^ n%512) 172288 group356 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group357 : List Block := [dataT29Column2Block1305,dataT29Column2Block1306,dataT29Column2Block1307,dataT29Column2Block1308,dataT29Column2Block1309,dataT29Column2Block1310,dataT29Column2Block1311,dataT29Column2Block1312]

theorem length357 : (group357.map Block.length).sum = 128 := by
  simp [group357,dataT29Column2Block1305,dataT29Column2Block1306,dataT29Column2Block1307,dataT29Column2Block1308,dataT29Column2Block1309,dataT29Column2Block1310,dataT29Column2Block1311,dataT29Column2Block1312,Block.length]

theorem checked357 : checkBlocks (fun n => n/512 ^^^ n%512) 172416 group357 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group358 : List Block := [dataT29Column2Block1313,dataT29Column2Block1314,dataT29Column2Block1315,dataT29Column2Block1316,dataT29Column2Block1317,dataT29Column2Block1318,dataT29Column2Block1319,dataT29Column2Block1320]

theorem length358 : (group358.map Block.length).sum = 128 := by
  simp [group358,dataT29Column2Block1313,dataT29Column2Block1314,dataT29Column2Block1315,dataT29Column2Block1316,dataT29Column2Block1317,dataT29Column2Block1318,dataT29Column2Block1319,dataT29Column2Block1320,Block.length]

theorem checked358 : checkBlocks (fun n => n/512 ^^^ n%512) 172544 group358 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group359 : List Block := [dataT29Column2Block1321,dataT29Column2Block1322,dataT29Column2Block1323,dataT29Column2Block1324,dataT29Column2Block1325,dataT29Column2Block1326,dataT29Column2Block1327,dataT29Column2Block1328]

theorem length359 : (group359.map Block.length).sum = 128 := by
  simp [group359,dataT29Column2Block1321,dataT29Column2Block1322,dataT29Column2Block1323,dataT29Column2Block1324,dataT29Column2Block1325,dataT29Column2Block1326,dataT29Column2Block1327,dataT29Column2Block1328,Block.length]

theorem checked359 : checkBlocks (fun n => n/512 ^^^ n%512) 172672 group359 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
