import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group112 : List Block := [dataT29Column2Block192,dataT29Column2Block193,dataT29Column2Block194,dataT29Column2Block195]

theorem length112 : (group112.map Block.length).sum = 512 := by
  simp [group112,dataT29Column2Block192,dataT29Column2Block193,dataT29Column2Block194,dataT29Column2Block195,Block.length]

theorem checked112 : checkBlocks (fun n => n/512 ^^^ n%512) 73728 group112 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group113 : List Block := [dataT29Column2Block196,dataT29Column2Block197,dataT29Column2Block198,dataT29Column2Block199]

theorem length113 : (group113.map Block.length).sum = 512 := by
  simp [group113,dataT29Column2Block196,dataT29Column2Block197,dataT29Column2Block198,dataT29Column2Block199,Block.length]

theorem checked113 : checkBlocks (fun n => n/512 ^^^ n%512) 74240 group113 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group114 : List Block := [dataT29Column2Block200,dataT29Column2Block201,dataT29Column2Block202,dataT29Column2Block203]

theorem length114 : (group114.map Block.length).sum = 512 := by
  simp [group114,dataT29Column2Block200,dataT29Column2Block201,dataT29Column2Block202,dataT29Column2Block203,Block.length]

theorem checked114 : checkBlocks (fun n => n/512 ^^^ n%512) 74752 group114 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group115 : List Block := [dataT29Column2Block204,dataT29Column2Block205,dataT29Column2Block206,dataT29Column2Block207]

theorem length115 : (group115.map Block.length).sum = 512 := by
  simp [group115,dataT29Column2Block204,dataT29Column2Block205,dataT29Column2Block206,dataT29Column2Block207,Block.length]

theorem checked115 : checkBlocks (fun n => n/512 ^^^ n%512) 75264 group115 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
