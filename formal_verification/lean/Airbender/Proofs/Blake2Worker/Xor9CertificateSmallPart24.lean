import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group128 : List Block := [dataT29Column2Block256,dataT29Column2Block257,dataT29Column2Block258,dataT29Column2Block259,dataT29Column2Block260,dataT29Column2Block261,dataT29Column2Block262,dataT29Column2Block263]

theorem length128 : (group128.map Block.length).sum = 256 := by
  simp [group128,dataT29Column2Block256,dataT29Column2Block257,dataT29Column2Block258,dataT29Column2Block259,dataT29Column2Block260,dataT29Column2Block261,dataT29Column2Block262,dataT29Column2Block263,Block.length]

theorem checked128 : checkBlocks (fun n => n/512 ^^^ n%512) 81920 group128 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group129 : List Block := [dataT29Column2Block264,dataT29Column2Block265,dataT29Column2Block266,dataT29Column2Block267,dataT29Column2Block268,dataT29Column2Block269,dataT29Column2Block270,dataT29Column2Block271]

theorem length129 : (group129.map Block.length).sum = 256 := by
  simp [group129,dataT29Column2Block264,dataT29Column2Block265,dataT29Column2Block266,dataT29Column2Block267,dataT29Column2Block268,dataT29Column2Block269,dataT29Column2Block270,dataT29Column2Block271,Block.length]

theorem checked129 : checkBlocks (fun n => n/512 ^^^ n%512) 82176 group129 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group130 : List Block := [dataT29Column2Block272,dataT29Column2Block273,dataT29Column2Block274,dataT29Column2Block275,dataT29Column2Block276,dataT29Column2Block277,dataT29Column2Block278,dataT29Column2Block279]

theorem length130 : (group130.map Block.length).sum = 256 := by
  simp [group130,dataT29Column2Block272,dataT29Column2Block273,dataT29Column2Block274,dataT29Column2Block275,dataT29Column2Block276,dataT29Column2Block277,dataT29Column2Block278,dataT29Column2Block279,Block.length]

theorem checked130 : checkBlocks (fun n => n/512 ^^^ n%512) 82432 group130 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group131 : List Block := [dataT29Column2Block280,dataT29Column2Block281,dataT29Column2Block282,dataT29Column2Block283,dataT29Column2Block284,dataT29Column2Block285,dataT29Column2Block286,dataT29Column2Block287]

theorem length131 : (group131.map Block.length).sum = 256 := by
  simp [group131,dataT29Column2Block280,dataT29Column2Block281,dataT29Column2Block282,dataT29Column2Block283,dataT29Column2Block284,dataT29Column2Block285,dataT29Column2Block286,dataT29Column2Block287,Block.length]

theorem checked131 : checkBlocks (fun n => n/512 ^^^ n%512) 82688 group131 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
