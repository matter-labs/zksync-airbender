import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group136 : List Block := [dataT29Column2Block320,dataT29Column2Block321,dataT29Column2Block322,dataT29Column2Block323,dataT29Column2Block324,dataT29Column2Block325,dataT29Column2Block326,dataT29Column2Block327]

theorem length136 : (group136.map Block.length).sum = 256 := by
  simp [group136,dataT29Column2Block320,dataT29Column2Block321,dataT29Column2Block322,dataT29Column2Block323,dataT29Column2Block324,dataT29Column2Block325,dataT29Column2Block326,dataT29Column2Block327,Block.length]

theorem checked136 : checkBlocks (fun n => n/512 ^^^ n%512) 83968 group136 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group137 : List Block := [dataT29Column2Block328,dataT29Column2Block329,dataT29Column2Block330,dataT29Column2Block331,dataT29Column2Block332,dataT29Column2Block333,dataT29Column2Block334,dataT29Column2Block335]

theorem length137 : (group137.map Block.length).sum = 256 := by
  simp [group137,dataT29Column2Block328,dataT29Column2Block329,dataT29Column2Block330,dataT29Column2Block331,dataT29Column2Block332,dataT29Column2Block333,dataT29Column2Block334,dataT29Column2Block335,Block.length]

theorem checked137 : checkBlocks (fun n => n/512 ^^^ n%512) 84224 group137 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group138 : List Block := [dataT29Column2Block336,dataT29Column2Block337,dataT29Column2Block338,dataT29Column2Block339,dataT29Column2Block340,dataT29Column2Block341,dataT29Column2Block342,dataT29Column2Block343]

theorem length138 : (group138.map Block.length).sum = 256 := by
  simp [group138,dataT29Column2Block336,dataT29Column2Block337,dataT29Column2Block338,dataT29Column2Block339,dataT29Column2Block340,dataT29Column2Block341,dataT29Column2Block342,dataT29Column2Block343,Block.length]

theorem checked138 : checkBlocks (fun n => n/512 ^^^ n%512) 84480 group138 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group139 : List Block := [dataT29Column2Block344,dataT29Column2Block345,dataT29Column2Block346,dataT29Column2Block347,dataT29Column2Block348,dataT29Column2Block349,dataT29Column2Block350,dataT29Column2Block351]

theorem length139 : (group139.map Block.length).sum = 256 := by
  simp [group139,dataT29Column2Block344,dataT29Column2Block345,dataT29Column2Block346,dataT29Column2Block347,dataT29Column2Block348,dataT29Column2Block349,dataT29Column2Block350,dataT29Column2Block351,Block.length]

theorem checked139 : checkBlocks (fun n => n/512 ^^^ n%512) 84736 group139 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
