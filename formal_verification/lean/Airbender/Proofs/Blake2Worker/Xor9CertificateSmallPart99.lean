import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group428 : List Block := [dataT29Column2Block1829,dataT29Column2Block1830,dataT29Column2Block1831,dataT29Column2Block1832]

theorem length428 : (group428.map Block.length).sum = 512 := by
  simp [group428,dataT29Column2Block1829,dataT29Column2Block1830,dataT29Column2Block1831,dataT29Column2Block1832,Block.length]

theorem checked428 : checkBlocks (fun n => n/512 ^^^ n%512) 184704 group428 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group429 : List Block := [dataT29Column2Block1833,dataT29Column2Block1834,dataT29Column2Block1835,dataT29Column2Block1836]

theorem length429 : (group429.map Block.length).sum = 512 := by
  simp [group429,dataT29Column2Block1833,dataT29Column2Block1834,dataT29Column2Block1835,dataT29Column2Block1836,Block.length]

theorem checked429 : checkBlocks (fun n => n/512 ^^^ n%512) 185216 group429 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group430 : List Block := [dataT29Column2Block1837,dataT29Column2Block1838,dataT29Column2Block1839,dataT29Column2Block1840]

theorem length430 : (group430.map Block.length).sum = 512 := by
  simp [group430,dataT29Column2Block1837,dataT29Column2Block1838,dataT29Column2Block1839,dataT29Column2Block1840,Block.length]

theorem checked430 : checkBlocks (fun n => n/512 ^^^ n%512) 185728 group430 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group431 : List Block := [dataT29Column2Block1841,dataT29Column2Block1842,dataT29Column2Block1843,dataT29Column2Block1844]

theorem length431 : (group431.map Block.length).sum = 512 := by
  simp [group431,dataT29Column2Block1841,dataT29Column2Block1842,dataT29Column2Block1843,dataT29Column2Block1844,Block.length]

theorem checked431 : checkBlocks (fun n => n/512 ^^^ n%512) 186240 group431 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
