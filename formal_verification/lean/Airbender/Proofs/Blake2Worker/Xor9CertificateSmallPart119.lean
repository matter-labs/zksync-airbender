import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group508 : List Block := [dataT29Column2Block1978]

theorem length508 : (group508.map Block.length).sum = 512 := by
  simp [group508,dataT29Column2Block1978,Block.length]

theorem checked508 : checkBlocks (fun n => n/512 ^^^ n%512) 225280 group508 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group509 : List Block := [dataT29Column2Block1979]

theorem length509 : (group509.map Block.length).sum = 512 := by
  simp [group509,dataT29Column2Block1979,Block.length]

theorem checked509 : checkBlocks (fun n => n/512 ^^^ n%512) 225792 group509 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group510 : List Block := [dataT29Column2Block1980]

theorem length510 : (group510.map Block.length).sum = 512 := by
  simp [group510,dataT29Column2Block1980,Block.length]

theorem checked510 : checkBlocks (fun n => n/512 ^^^ n%512) 226304 group510 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group511 : List Block := [dataT29Column2Block1981]

theorem length511 : (group511.map Block.length).sum = 512 := by
  simp [group511,dataT29Column2Block1981,Block.length]

theorem checked511 : checkBlocks (fun n => n/512 ^^^ n%512) 226816 group511 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
