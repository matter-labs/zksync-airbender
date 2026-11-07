import Airbender.Proofs.Blake2Worker.Xor9Dense1537
import Mathlib.Tactic.FinCases
import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group384 : List Block := [dataT29Column2Block1521,dataT29Column2Block1522,dataT29Column2Block1523,dataT29Column2Block1524,dataT29Column2Block1525,dataT29Column2Block1526,dataT29Column2Block1527,dataT29Column2Block1528]

theorem length384 : (group384.map Block.length).sum = 32 := by
  simp [group384,dataT29Column2Block1521,dataT29Column2Block1522,dataT29Column2Block1523,dataT29Column2Block1524,dataT29Column2Block1525,dataT29Column2Block1526,dataT29Column2Block1527,dataT29Column2Block1528,Block.length]

theorem checked384 : checkBlocks (fun n => n/512 ^^^ n%512) 174528 group384 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group385 : List Block := [dataT29Column2Block1529,dataT29Column2Block1530,dataT29Column2Block1531,dataT29Column2Block1532,dataT29Column2Block1533,dataT29Column2Block1534,dataT29Column2Block1535,dataT29Column2Block1536]

theorem length385 : (group385.map Block.length).sum = 32 := by
  simp [group385,dataT29Column2Block1529,dataT29Column2Block1530,dataT29Column2Block1531,dataT29Column2Block1532,dataT29Column2Block1533,dataT29Column2Block1534,dataT29Column2Block1535,dataT29Column2Block1536,Block.length]

theorem checked385 : checkBlocks (fun n => n/512 ^^^ n%512) 174560 group385 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group386 : List Block := [dataT29Column2Block1537]

theorem length386 : (group386.map Block.length).sum = 512 :=
  (singleton_length dataT29Column2Block1537).trans Xor9Dense1537.length

theorem checked386 : checkBlocks (fun n => n/512 ^^^ n%512) 174592 group386 = true :=
  check_singleton_of_size _ _ _ 512 Xor9Dense1537.length Xor9Dense1537.reads

def group387 : List Block := [dataT29Column2Block1538,dataT29Column2Block1539,dataT29Column2Block1540,dataT29Column2Block1541,dataT29Column2Block1542,dataT29Column2Block1543,dataT29Column2Block1544,dataT29Column2Block1545]

theorem length387 : (group387.map Block.length).sum = 64 := by
  simp [group387,dataT29Column2Block1538,dataT29Column2Block1539,dataT29Column2Block1540,dataT29Column2Block1541,dataT29Column2Block1542,dataT29Column2Block1543,dataT29Column2Block1544,dataT29Column2Block1545,Block.length]

theorem checked387 : checkBlocks (fun n => n/512 ^^^ n%512) 175104 group387 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
