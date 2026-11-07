import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group456 : List Block := [dataT29Column2Block1926]

theorem length456 : (group456.map Block.length).sum = 512 := by
  simp [group456,dataT29Column2Block1926,Block.length]

theorem checked456 : checkBlocks (fun n => n/512 ^^^ n%512) 198656 group456 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group457 : List Block := [dataT29Column2Block1927]

theorem length457 : (group457.map Block.length).sum = 512 := by
  simp [group457,dataT29Column2Block1927,Block.length]

theorem checked457 : checkBlocks (fun n => n/512 ^^^ n%512) 199168 group457 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group458 : List Block := [dataT29Column2Block1928]

theorem length458 : (group458.map Block.length).sum = 512 := by
  simp [group458,dataT29Column2Block1928,Block.length]

theorem checked458 : checkBlocks (fun n => n/512 ^^^ n%512) 199680 group458 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group459 : List Block := [dataT29Column2Block1929]

theorem length459 : (group459.map Block.length).sum = 512 := by
  simp [group459,dataT29Column2Block1929,Block.length]

theorem checked459 : checkBlocks (fun n => n/512 ^^^ n%512) 200192 group459 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
