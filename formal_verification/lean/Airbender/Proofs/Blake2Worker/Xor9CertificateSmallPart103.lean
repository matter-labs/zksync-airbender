import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group444 : List Block := [dataT29Column2Block1893,dataT29Column2Block1894,dataT29Column2Block1895,dataT29Column2Block1896]

theorem length444 : (group444.map Block.length).sum = 512 := by
  simp [group444,dataT29Column2Block1893,dataT29Column2Block1894,dataT29Column2Block1895,dataT29Column2Block1896,Block.length]

theorem checked444 : checkBlocks (fun n => n/512 ^^^ n%512) 192896 group444 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group445 : List Block := [dataT29Column2Block1897,dataT29Column2Block1898,dataT29Column2Block1899,dataT29Column2Block1900]

theorem length445 : (group445.map Block.length).sum = 512 := by
  simp [group445,dataT29Column2Block1897,dataT29Column2Block1898,dataT29Column2Block1899,dataT29Column2Block1900,Block.length]

theorem checked445 : checkBlocks (fun n => n/512 ^^^ n%512) 193408 group445 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group446 : List Block := [dataT29Column2Block1901,dataT29Column2Block1902,dataT29Column2Block1903,dataT29Column2Block1904]

theorem length446 : (group446.map Block.length).sum = 512 := by
  simp [group446,dataT29Column2Block1901,dataT29Column2Block1902,dataT29Column2Block1903,dataT29Column2Block1904,Block.length]

theorem checked446 : checkBlocks (fun n => n/512 ^^^ n%512) 193920 group446 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group447 : List Block := [dataT29Column2Block1905,dataT29Column2Block1906,dataT29Column2Block1907,dataT29Column2Block1908]

theorem length447 : (group447.map Block.length).sum = 512 := by
  simp [group447,dataT29Column2Block1905,dataT29Column2Block1906,dataT29Column2Block1907,dataT29Column2Block1908,Block.length]

theorem checked447 : checkBlocks (fun n => n/512 ^^^ n%512) 194432 group447 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
