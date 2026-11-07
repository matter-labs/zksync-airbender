import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group172 : List Block := [dataT29Column2Block600,dataT29Column2Block601,dataT29Column2Block602,dataT29Column2Block603,dataT29Column2Block604,dataT29Column2Block605,dataT29Column2Block606,dataT29Column2Block607]

theorem length172 : (group172.map Block.length).sum = 32 := by
  simp [group172,dataT29Column2Block600,dataT29Column2Block601,dataT29Column2Block602,dataT29Column2Block603,dataT29Column2Block604,dataT29Column2Block605,dataT29Column2Block606,dataT29Column2Block607,Block.length]

theorem checked172 : checkBlocks (fun n => n/512 ^^^ n%512) 87900 group172 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group173 : List Block := [dataT29Column2Block608,dataT29Column2Block609,dataT29Column2Block610,dataT29Column2Block611,dataT29Column2Block612,dataT29Column2Block613,dataT29Column2Block614,dataT29Column2Block615]

theorem length173 : (group173.map Block.length).sum = 32 := by
  simp [group173,dataT29Column2Block608,dataT29Column2Block609,dataT29Column2Block610,dataT29Column2Block611,dataT29Column2Block612,dataT29Column2Block613,dataT29Column2Block614,dataT29Column2Block615,Block.length]

theorem checked173 : checkBlocks (fun n => n/512 ^^^ n%512) 87932 group173 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group174 : List Block := [dataT29Column2Block616,dataT29Column2Block617,dataT29Column2Block618,dataT29Column2Block619,dataT29Column2Block620,dataT29Column2Block621,dataT29Column2Block622,dataT29Column2Block623]

theorem length174 : (group174.map Block.length).sum = 32 := by
  simp [group174,dataT29Column2Block616,dataT29Column2Block617,dataT29Column2Block618,dataT29Column2Block619,dataT29Column2Block620,dataT29Column2Block621,dataT29Column2Block622,dataT29Column2Block623,Block.length]

theorem checked174 : checkBlocks (fun n => n/512 ^^^ n%512) 87964 group174 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group175 : List Block := [dataT29Column2Block624,dataT29Column2Block625,dataT29Column2Block626,dataT29Column2Block627,dataT29Column2Block628,dataT29Column2Block629,dataT29Column2Block630,dataT29Column2Block631]

theorem length175 : (group175.map Block.length).sum = 32 := by
  simp [group175,dataT29Column2Block624,dataT29Column2Block625,dataT29Column2Block626,dataT29Column2Block627,dataT29Column2Block628,dataT29Column2Block629,dataT29Column2Block630,dataT29Column2Block631,Block.length]

theorem checked175 : checkBlocks (fun n => n/512 ^^^ n%512) 87996 group175 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
