import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group540 : List Block := [dataT29Column2Block2010]

theorem length540 : (group540.map Block.length).sum = 512 := by
  simp [group540,dataT29Column2Block2010,Block.length]

theorem checked540 : checkBlocks (fun n => n/512 ^^^ n%512) 241664 group540 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group541 : List Block := [dataT29Column2Block2011]

theorem length541 : (group541.map Block.length).sum = 512 := by
  simp [group541,dataT29Column2Block2011,Block.length]

theorem checked541 : checkBlocks (fun n => n/512 ^^^ n%512) 242176 group541 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group542 : List Block := [dataT29Column2Block2012]

theorem length542 : (group542.map Block.length).sum = 512 := by
  simp [group542,dataT29Column2Block2012,Block.length]

theorem checked542 : checkBlocks (fun n => n/512 ^^^ n%512) 242688 group542 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group543 : List Block := [dataT29Column2Block2013]

theorem length543 : (group543.map Block.length).sum = 512 := by
  simp [group543,dataT29Column2Block2013,Block.length]

theorem checked543 : checkBlocks (fun n => n/512 ^^^ n%512) 243200 group543 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
