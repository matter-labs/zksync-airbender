import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group468 : List Block := [dataT29Column2Block1938]

theorem length468 : (group468.map Block.length).sum = 512 := by
  simp [group468,dataT29Column2Block1938,Block.length]

theorem checked468 : checkBlocks (fun n => n/512 ^^^ n%512) 204800 group468 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group469 : List Block := [dataT29Column2Block1939]

theorem length469 : (group469.map Block.length).sum = 512 := by
  simp [group469,dataT29Column2Block1939,Block.length]

theorem checked469 : checkBlocks (fun n => n/512 ^^^ n%512) 205312 group469 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group470 : List Block := [dataT29Column2Block1940]

theorem length470 : (group470.map Block.length).sum = 512 := by
  simp [group470,dataT29Column2Block1940,Block.length]

theorem checked470 : checkBlocks (fun n => n/512 ^^^ n%512) 205824 group470 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group471 : List Block := [dataT29Column2Block1941]

theorem length471 : (group471.map Block.length).sum = 512 := by
  simp [group471,dataT29Column2Block1941,Block.length]

theorem checked471 : checkBlocks (fun n => n/512 ^^^ n%512) 206336 group471 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
