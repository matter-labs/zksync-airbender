import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData29

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group4 : List Block := [dataT29Column2Block8,dataT29Column2Block9]

theorem length4 : (group4.map Block.length).sum = 1024 := by
  simp [group4,dataT29Column2Block8,dataT29Column2Block9,Block.length]

theorem checked4 : checkBlocks (fun n => n/512 ^^^ n%512) 4096 group4 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group5 : List Block := [dataT29Column2Block10,dataT29Column2Block11]

theorem length5 : (group5.map Block.length).sum = 1024 := by
  simp [group5,dataT29Column2Block10,dataT29Column2Block11,Block.length]

theorem checked5 : checkBlocks (fun n => n/512 ^^^ n%512) 5120 group5 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group6 : List Block := [dataT29Column2Block12,dataT29Column2Block13]

theorem length6 : (group6.map Block.length).sum = 1024 := by
  simp [group6,dataT29Column2Block12,dataT29Column2Block13,Block.length]

theorem checked6 : checkBlocks (fun n => n/512 ^^^ n%512) 6144 group6 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group7 : List Block := [dataT29Column2Block14,dataT29Column2Block15]

theorem length7 : (group7.map Block.length).sum = 1024 := by
  simp [group7,dataT29Column2Block14,dataT29Column2Block15,Block.length]

theorem checked7 : checkBlocks (fun n => n/512 ^^^ n%512) 7168 group7 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
