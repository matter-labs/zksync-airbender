import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group8 : List Block := [dataT29Column2Block16,dataT29Column2Block17]

theorem length8 : (group8.map Block.length).sum = 1024 := by
  simp [group8,dataT29Column2Block16,dataT29Column2Block17,Block.length]

theorem checked8 : checkBlocks (fun n => n/512 ^^^ n%512) 8192 group8 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group9 : List Block := [dataT29Column2Block18,dataT29Column2Block19]

theorem length9 : (group9.map Block.length).sum = 1024 := by
  simp [group9,dataT29Column2Block18,dataT29Column2Block19,Block.length]

theorem checked9 : checkBlocks (fun n => n/512 ^^^ n%512) 9216 group9 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group10 : List Block := [dataT29Column2Block20,dataT29Column2Block21]

theorem length10 : (group10.map Block.length).sum = 1024 := by
  simp [group10,dataT29Column2Block20,dataT29Column2Block21,Block.length]

theorem checked10 : checkBlocks (fun n => n/512 ^^^ n%512) 10240 group10 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group11 : List Block := [dataT29Column2Block22,dataT29Column2Block23]

theorem length11 : (group11.map Block.length).sum = 1024 := by
  simp [group11,dataT29Column2Block22,dataT29Column2Block23,Block.length]

theorem checked11 : checkBlocks (fun n => n/512 ^^^ n%512) 11264 group11 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
