import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group52 : List Block := [dataT29Column2Block84]

theorem length52 : (group52.map Block.length).sum = 512 := by
  simp [group52,dataT29Column2Block84,Block.length]

theorem checked52 : checkBlocks (fun n => n/512 ^^^ n%512) 43008 group52 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group53 : List Block := [dataT29Column2Block85]

theorem length53 : (group53.map Block.length).sum = 512 := by
  simp [group53,dataT29Column2Block85,Block.length]

theorem checked53 : checkBlocks (fun n => n/512 ^^^ n%512) 43520 group53 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group54 : List Block := [dataT29Column2Block86]

theorem length54 : (group54.map Block.length).sum = 512 := by
  simp [group54,dataT29Column2Block86,Block.length]

theorem checked54 : checkBlocks (fun n => n/512 ^^^ n%512) 44032 group54 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group55 : List Block := [dataT29Column2Block87]

theorem length55 : (group55.map Block.length).sum = 512 := by
  simp [group55,dataT29Column2Block87,Block.length]

theorem checked55 : checkBlocks (fun n => n/512 ^^^ n%512) 44544 group55 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
