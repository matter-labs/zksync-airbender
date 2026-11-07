import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group120 : List Block := [dataT29Column2Block224,dataT29Column2Block225,dataT29Column2Block226,dataT29Column2Block227]

theorem length120 : (group120.map Block.length).sum = 512 := by
  simp [group120,dataT29Column2Block224,dataT29Column2Block225,dataT29Column2Block226,dataT29Column2Block227,Block.length]

theorem checked120 : checkBlocks (fun n => n/512 ^^^ n%512) 77824 group120 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group121 : List Block := [dataT29Column2Block228,dataT29Column2Block229,dataT29Column2Block230,dataT29Column2Block231]

theorem length121 : (group121.map Block.length).sum = 512 := by
  simp [group121,dataT29Column2Block228,dataT29Column2Block229,dataT29Column2Block230,dataT29Column2Block231,Block.length]

theorem checked121 : checkBlocks (fun n => n/512 ^^^ n%512) 78336 group121 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group122 : List Block := [dataT29Column2Block232,dataT29Column2Block233,dataT29Column2Block234,dataT29Column2Block235]

theorem length122 : (group122.map Block.length).sum = 512 := by
  simp [group122,dataT29Column2Block232,dataT29Column2Block233,dataT29Column2Block234,dataT29Column2Block235,Block.length]

theorem checked122 : checkBlocks (fun n => n/512 ^^^ n%512) 78848 group122 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group123 : List Block := [dataT29Column2Block236,dataT29Column2Block237,dataT29Column2Block238,dataT29Column2Block239]

theorem length123 : (group123.map Block.length).sum = 512 := by
  simp [group123,dataT29Column2Block236,dataT29Column2Block237,dataT29Column2Block238,dataT29Column2Block239,Block.length]

theorem checked123 : checkBlocks (fun n => n/512 ^^^ n%512) 79360 group123 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
