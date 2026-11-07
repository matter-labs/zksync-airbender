import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group132 : List Block := [dataT29Column2Block288,dataT29Column2Block289,dataT29Column2Block290,dataT29Column2Block291,dataT29Column2Block292,dataT29Column2Block293,dataT29Column2Block294,dataT29Column2Block295]

theorem length132 : (group132.map Block.length).sum = 256 := by
  simp [group132,dataT29Column2Block288,dataT29Column2Block289,dataT29Column2Block290,dataT29Column2Block291,dataT29Column2Block292,dataT29Column2Block293,dataT29Column2Block294,dataT29Column2Block295,Block.length]

theorem checked132 : checkBlocks (fun n => n/512 ^^^ n%512) 82944 group132 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group133 : List Block := [dataT29Column2Block296,dataT29Column2Block297,dataT29Column2Block298,dataT29Column2Block299,dataT29Column2Block300,dataT29Column2Block301,dataT29Column2Block302,dataT29Column2Block303]

theorem length133 : (group133.map Block.length).sum = 256 := by
  simp [group133,dataT29Column2Block296,dataT29Column2Block297,dataT29Column2Block298,dataT29Column2Block299,dataT29Column2Block300,dataT29Column2Block301,dataT29Column2Block302,dataT29Column2Block303,Block.length]

theorem checked133 : checkBlocks (fun n => n/512 ^^^ n%512) 83200 group133 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group134 : List Block := [dataT29Column2Block304,dataT29Column2Block305,dataT29Column2Block306,dataT29Column2Block307,dataT29Column2Block308,dataT29Column2Block309,dataT29Column2Block310,dataT29Column2Block311]

theorem length134 : (group134.map Block.length).sum = 256 := by
  simp [group134,dataT29Column2Block304,dataT29Column2Block305,dataT29Column2Block306,dataT29Column2Block307,dataT29Column2Block308,dataT29Column2Block309,dataT29Column2Block310,dataT29Column2Block311,Block.length]

theorem checked134 : checkBlocks (fun n => n/512 ^^^ n%512) 83456 group134 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group135 : List Block := [dataT29Column2Block312,dataT29Column2Block313,dataT29Column2Block314,dataT29Column2Block315,dataT29Column2Block316,dataT29Column2Block317,dataT29Column2Block318,dataT29Column2Block319]

theorem length135 : (group135.map Block.length).sum = 256 := by
  simp [group135,dataT29Column2Block312,dataT29Column2Block313,dataT29Column2Block314,dataT29Column2Block315,dataT29Column2Block316,dataT29Column2Block317,dataT29Column2Block318,dataT29Column2Block319,Block.length]

theorem checked135 : checkBlocks (fun n => n/512 ^^^ n%512) 83712 group135 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
