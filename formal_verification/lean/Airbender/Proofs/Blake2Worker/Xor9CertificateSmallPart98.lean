import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group424 : List Block := [dataT29Column2Block1813,dataT29Column2Block1814,dataT29Column2Block1815,dataT29Column2Block1816]

theorem length424 : (group424.map Block.length).sum = 512 := by
  simp [group424,dataT29Column2Block1813,dataT29Column2Block1814,dataT29Column2Block1815,dataT29Column2Block1816,Block.length]

theorem checked424 : checkBlocks (fun n => n/512 ^^^ n%512) 182656 group424 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group425 : List Block := [dataT29Column2Block1817,dataT29Column2Block1818,dataT29Column2Block1819,dataT29Column2Block1820]

theorem length425 : (group425.map Block.length).sum = 512 := by
  simp [group425,dataT29Column2Block1817,dataT29Column2Block1818,dataT29Column2Block1819,dataT29Column2Block1820,Block.length]

theorem checked425 : checkBlocks (fun n => n/512 ^^^ n%512) 183168 group425 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group426 : List Block := [dataT29Column2Block1821,dataT29Column2Block1822,dataT29Column2Block1823,dataT29Column2Block1824]

theorem length426 : (group426.map Block.length).sum = 512 := by
  simp [group426,dataT29Column2Block1821,dataT29Column2Block1822,dataT29Column2Block1823,dataT29Column2Block1824,Block.length]

theorem checked426 : checkBlocks (fun n => n/512 ^^^ n%512) 183680 group426 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group427 : List Block := [dataT29Column2Block1825,dataT29Column2Block1826,dataT29Column2Block1827,dataT29Column2Block1828]

theorem length427 : (group427.map Block.length).sum = 512 := by
  simp [group427,dataT29Column2Block1825,dataT29Column2Block1826,dataT29Column2Block1827,dataT29Column2Block1828,Block.length]

theorem checked427 : checkBlocks (fun n => n/512 ^^^ n%512) 184192 group427 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
