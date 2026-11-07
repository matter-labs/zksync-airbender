import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group92 : List Block := [dataT29Column2Block124]

theorem length92 : (group92.map Block.length).sum = 512 := by
  simp [group92,dataT29Column2Block124,Block.length]

theorem checked92 : checkBlocks (fun n => n/512 ^^^ n%512) 63488 group92 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group93 : List Block := [dataT29Column2Block125]

theorem length93 : (group93.map Block.length).sum = 512 := by
  simp [group93,dataT29Column2Block125,Block.length]

theorem checked93 : checkBlocks (fun n => n/512 ^^^ n%512) 64000 group93 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group94 : List Block := [dataT29Column2Block126]

theorem length94 : (group94.map Block.length).sum = 512 := by
  simp [group94,dataT29Column2Block126,Block.length]

theorem checked94 : checkBlocks (fun n => n/512 ^^^ n%512) 64512 group94 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group95 : List Block := [dataT29Column2Block127]

theorem length95 : (group95.map Block.length).sum = 512 := by
  simp [group95,dataT29Column2Block127,Block.length]

theorem checked95 : checkBlocks (fun n => n/512 ^^^ n%512) 65024 group95 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
