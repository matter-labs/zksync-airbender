import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group368 : List Block := [dataT29Column2Block1393,dataT29Column2Block1394,dataT29Column2Block1395,dataT29Column2Block1396,dataT29Column2Block1397,dataT29Column2Block1398,dataT29Column2Block1399,dataT29Column2Block1400]

theorem length368 : (group368.map Block.length).sum = 128 := by
  simp [group368,dataT29Column2Block1393,dataT29Column2Block1394,dataT29Column2Block1395,dataT29Column2Block1396,dataT29Column2Block1397,dataT29Column2Block1398,dataT29Column2Block1399,dataT29Column2Block1400,Block.length]

theorem checked368 : checkBlocks (fun n => n/512 ^^^ n%512) 173824 group368 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group369 : List Block := [dataT29Column2Block1401,dataT29Column2Block1402,dataT29Column2Block1403,dataT29Column2Block1404,dataT29Column2Block1405,dataT29Column2Block1406,dataT29Column2Block1407,dataT29Column2Block1408]

theorem length369 : (group369.map Block.length).sum = 128 := by
  simp [group369,dataT29Column2Block1401,dataT29Column2Block1402,dataT29Column2Block1403,dataT29Column2Block1404,dataT29Column2Block1405,dataT29Column2Block1406,dataT29Column2Block1407,dataT29Column2Block1408,Block.length]

theorem checked369 : checkBlocks (fun n => n/512 ^^^ n%512) 173952 group369 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group370 : List Block := [dataT29Column2Block1409,dataT29Column2Block1410,dataT29Column2Block1411,dataT29Column2Block1412,dataT29Column2Block1413,dataT29Column2Block1414,dataT29Column2Block1415,dataT29Column2Block1416]

theorem length370 : (group370.map Block.length).sum = 32 := by
  simp [group370,dataT29Column2Block1409,dataT29Column2Block1410,dataT29Column2Block1411,dataT29Column2Block1412,dataT29Column2Block1413,dataT29Column2Block1414,dataT29Column2Block1415,dataT29Column2Block1416,Block.length]

theorem checked370 : checkBlocks (fun n => n/512 ^^^ n%512) 174080 group370 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group371 : List Block := [dataT29Column2Block1417,dataT29Column2Block1418,dataT29Column2Block1419,dataT29Column2Block1420,dataT29Column2Block1421,dataT29Column2Block1422,dataT29Column2Block1423,dataT29Column2Block1424]

theorem length371 : (group371.map Block.length).sum = 32 := by
  simp [group371,dataT29Column2Block1417,dataT29Column2Block1418,dataT29Column2Block1419,dataT29Column2Block1420,dataT29Column2Block1421,dataT29Column2Block1422,dataT29Column2Block1423,dataT29Column2Block1424,Block.length]

theorem checked371 : checkBlocks (fun n => n/512 ^^^ n%512) 174112 group371 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
