import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group232 : List Block := [dataT29Column2Block942,dataT29Column2Block943]

theorem length232 : (group232.map Block.length).sum = 512 := by
  simp [group232,dataT29Column2Block942,dataT29Column2Block943,Block.length]

theorem checked232 : checkBlocks (fun n => n/512 ^^^ n%512) 109824 group232 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group233 : List Block := [dataT29Column2Block944,dataT29Column2Block945]

theorem length233 : (group233.map Block.length).sum = 512 := by
  simp [group233,dataT29Column2Block944,dataT29Column2Block945,Block.length]

theorem checked233 : checkBlocks (fun n => n/512 ^^^ n%512) 110336 group233 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group234 : List Block := [dataT29Column2Block946,dataT29Column2Block947]

theorem length234 : (group234.map Block.length).sum = 512 := by
  simp [group234,dataT29Column2Block946,dataT29Column2Block947,Block.length]

theorem checked234 : checkBlocks (fun n => n/512 ^^^ n%512) 110848 group234 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group235 : List Block := [dataT29Column2Block948,dataT29Column2Block949]

theorem length235 : (group235.map Block.length).sum = 512 := by
  simp [group235,dataT29Column2Block948,dataT29Column2Block949,Block.length]

theorem checked235 : checkBlocks (fun n => n/512 ^^^ n%512) 111360 group235 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
