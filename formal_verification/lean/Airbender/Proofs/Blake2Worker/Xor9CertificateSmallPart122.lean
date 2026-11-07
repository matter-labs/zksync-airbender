import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group520 : List Block := [dataT29Column2Block1990]

theorem length520 : (group520.map Block.length).sum = 512 := by
  simp [group520,dataT29Column2Block1990,Block.length]

theorem checked520 : checkBlocks (fun n => n/512 ^^^ n%512) 231424 group520 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group521 : List Block := [dataT29Column2Block1991]

theorem length521 : (group521.map Block.length).sum = 512 := by
  simp [group521,dataT29Column2Block1991,Block.length]

theorem checked521 : checkBlocks (fun n => n/512 ^^^ n%512) 231936 group521 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group522 : List Block := [dataT29Column2Block1992]

theorem length522 : (group522.map Block.length).sum = 512 := by
  simp [group522,dataT29Column2Block1992,Block.length]

theorem checked522 : checkBlocks (fun n => n/512 ^^^ n%512) 232448 group522 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group523 : List Block := [dataT29Column2Block1993]

theorem length523 : (group523.map Block.length).sum = 512 := by
  simp [group523,dataT29Column2Block1993,Block.length]

theorem checked523 : checkBlocks (fun n => n/512 ^^^ n%512) 232960 group523 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
