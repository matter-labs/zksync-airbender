import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group436 : List Block := [dataT29Column2Block1861,dataT29Column2Block1862,dataT29Column2Block1863,dataT29Column2Block1864]

theorem length436 : (group436.map Block.length).sum = 512 := by
  simp [group436,dataT29Column2Block1861,dataT29Column2Block1862,dataT29Column2Block1863,dataT29Column2Block1864,Block.length]

theorem checked436 : checkBlocks (fun n => n/512 ^^^ n%512) 188800 group436 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group437 : List Block := [dataT29Column2Block1865,dataT29Column2Block1866,dataT29Column2Block1867,dataT29Column2Block1868]

theorem length437 : (group437.map Block.length).sum = 512 := by
  simp [group437,dataT29Column2Block1865,dataT29Column2Block1866,dataT29Column2Block1867,dataT29Column2Block1868,Block.length]

theorem checked437 : checkBlocks (fun n => n/512 ^^^ n%512) 189312 group437 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group438 : List Block := [dataT29Column2Block1869,dataT29Column2Block1870,dataT29Column2Block1871,dataT29Column2Block1872]

theorem length438 : (group438.map Block.length).sum = 512 := by
  simp [group438,dataT29Column2Block1869,dataT29Column2Block1870,dataT29Column2Block1871,dataT29Column2Block1872,Block.length]

theorem checked438 : checkBlocks (fun n => n/512 ^^^ n%512) 189824 group438 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group439 : List Block := [dataT29Column2Block1873,dataT29Column2Block1874,dataT29Column2Block1875,dataT29Column2Block1876]

theorem length439 : (group439.map Block.length).sum = 512 := by
  simp [group439,dataT29Column2Block1873,dataT29Column2Block1874,dataT29Column2Block1875,dataT29Column2Block1876,Block.length]

theorem checked439 : checkBlocks (fun n => n/512 ^^^ n%512) 190336 group439 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
