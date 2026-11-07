import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group124 : List Block := [dataT29Column2Block240,dataT29Column2Block241,dataT29Column2Block242,dataT29Column2Block243]

theorem length124 : (group124.map Block.length).sum = 512 := by
  simp [group124,dataT29Column2Block240,dataT29Column2Block241,dataT29Column2Block242,dataT29Column2Block243,Block.length]

theorem checked124 : checkBlocks (fun n => n/512 ^^^ n%512) 79872 group124 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group125 : List Block := [dataT29Column2Block244,dataT29Column2Block245,dataT29Column2Block246,dataT29Column2Block247]

theorem length125 : (group125.map Block.length).sum = 512 := by
  simp [group125,dataT29Column2Block244,dataT29Column2Block245,dataT29Column2Block246,dataT29Column2Block247,Block.length]

theorem checked125 : checkBlocks (fun n => n/512 ^^^ n%512) 80384 group125 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group126 : List Block := [dataT29Column2Block248,dataT29Column2Block249,dataT29Column2Block250,dataT29Column2Block251]

theorem length126 : (group126.map Block.length).sum = 512 := by
  simp [group126,dataT29Column2Block248,dataT29Column2Block249,dataT29Column2Block250,dataT29Column2Block251,Block.length]

theorem checked126 : checkBlocks (fun n => n/512 ^^^ n%512) 80896 group126 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group127 : List Block := [dataT29Column2Block252,dataT29Column2Block253,dataT29Column2Block254,dataT29Column2Block255]

theorem length127 : (group127.map Block.length).sum = 512 := by
  simp [group127,dataT29Column2Block252,dataT29Column2Block253,dataT29Column2Block254,dataT29Column2Block255,Block.length]

theorem checked127 : checkBlocks (fun n => n/512 ^^^ n%512) 81408 group127 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
