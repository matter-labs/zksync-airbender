import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group464 : List Block := [dataT29Column2Block1934]

theorem length464 : (group464.map Block.length).sum = 512 := by
  simp [group464,dataT29Column2Block1934,Block.length]

theorem checked464 : checkBlocks (fun n => n/512 ^^^ n%512) 202752 group464 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group465 : List Block := [dataT29Column2Block1935]

theorem length465 : (group465.map Block.length).sum = 512 := by
  simp [group465,dataT29Column2Block1935,Block.length]

theorem checked465 : checkBlocks (fun n => n/512 ^^^ n%512) 203264 group465 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group466 : List Block := [dataT29Column2Block1936]

theorem length466 : (group466.map Block.length).sum = 512 := by
  simp [group466,dataT29Column2Block1936,Block.length]

theorem checked466 : checkBlocks (fun n => n/512 ^^^ n%512) 203776 group466 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group467 : List Block := [dataT29Column2Block1937]

theorem length467 : (group467.map Block.length).sum = 512 := by
  simp [group467,dataT29Column2Block1937,Block.length]

theorem checked467 : checkBlocks (fun n => n/512 ^^^ n%512) 204288 group467 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
