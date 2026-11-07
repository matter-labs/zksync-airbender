import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group16 : List Block := [dataT29Column2Block32,dataT29Column2Block33]

theorem length16 : (group16.map Block.length).sum = 1024 := by
  simp [group16,dataT29Column2Block32,dataT29Column2Block33,Block.length]

theorem checked16 : checkBlocks (fun n => n/512 ^^^ n%512) 16384 group16 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group17 : List Block := [dataT29Column2Block34,dataT29Column2Block35]

theorem length17 : (group17.map Block.length).sum = 1024 := by
  simp [group17,dataT29Column2Block34,dataT29Column2Block35,Block.length]

theorem checked17 : checkBlocks (fun n => n/512 ^^^ n%512) 17408 group17 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group18 : List Block := [dataT29Column2Block36,dataT29Column2Block37]

theorem length18 : (group18.map Block.length).sum = 1024 := by
  simp [group18,dataT29Column2Block36,dataT29Column2Block37,Block.length]

theorem checked18 : checkBlocks (fun n => n/512 ^^^ n%512) 18432 group18 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group19 : List Block := [dataT29Column2Block38,dataT29Column2Block39]

theorem length19 : (group19.map Block.length).sum = 1024 := by
  simp [group19,dataT29Column2Block38,dataT29Column2Block39,Block.length]

theorem checked19 : checkBlocks (fun n => n/512 ^^^ n%512) 19456 group19 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
