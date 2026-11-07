import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group28 : List Block := [dataT29Column2Block56,dataT29Column2Block57]

theorem length28 : (group28.map Block.length).sum = 1024 := by
  simp [group28,dataT29Column2Block56,dataT29Column2Block57,Block.length]

theorem checked28 : checkBlocks (fun n => n/512 ^^^ n%512) 28672 group28 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group29 : List Block := [dataT29Column2Block58,dataT29Column2Block59]

theorem length29 : (group29.map Block.length).sum = 1024 := by
  simp [group29,dataT29Column2Block58,dataT29Column2Block59,Block.length]

theorem checked29 : checkBlocks (fun n => n/512 ^^^ n%512) 29696 group29 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group30 : List Block := [dataT29Column2Block60,dataT29Column2Block61]

theorem length30 : (group30.map Block.length).sum = 1024 := by
  simp [group30,dataT29Column2Block60,dataT29Column2Block61,Block.length]

theorem checked30 : checkBlocks (fun n => n/512 ^^^ n%512) 30720 group30 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group31 : List Block := [dataT29Column2Block62,dataT29Column2Block63]

theorem length31 : (group31.map Block.length).sum = 1024 := by
  simp [group31,dataT29Column2Block62,dataT29Column2Block63,Block.length]

theorem checked31 : checkBlocks (fun n => n/512 ^^^ n%512) 31744 group31 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
