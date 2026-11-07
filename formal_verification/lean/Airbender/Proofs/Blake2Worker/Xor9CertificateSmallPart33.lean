import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group164 : List Block := [dataT29Column2Block537,dataT29Column2Block538,dataT29Column2Block539,dataT29Column2Block540,dataT29Column2Block541,dataT29Column2Block542,dataT29Column2Block543,dataT29Column2Block544]

theorem length164 : (group164.map Block.length).sum = 32 := by
  simp [group164,dataT29Column2Block537,dataT29Column2Block538,dataT29Column2Block539,dataT29Column2Block540,dataT29Column2Block541,dataT29Column2Block542,dataT29Column2Block543,dataT29Column2Block544,Block.length]

theorem checked164 : checkBlocks (fun n => n/512 ^^^ n%512) 87648 group164 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group165 : List Block := [dataT29Column2Block545,dataT29Column2Block546,dataT29Column2Block547,dataT29Column2Block548,dataT29Column2Block549,dataT29Column2Block550,dataT29Column2Block551,dataT29Column2Block552]

theorem length165 : (group165.map Block.length).sum = 32 := by
  simp [group165,dataT29Column2Block545,dataT29Column2Block546,dataT29Column2Block547,dataT29Column2Block548,dataT29Column2Block549,dataT29Column2Block550,dataT29Column2Block551,dataT29Column2Block552,Block.length]

theorem checked165 : checkBlocks (fun n => n/512 ^^^ n%512) 87680 group165 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group166 : List Block := [dataT29Column2Block553,dataT29Column2Block554,dataT29Column2Block555,dataT29Column2Block556,dataT29Column2Block557,dataT29Column2Block558,dataT29Column2Block559,dataT29Column2Block560]

theorem length166 : (group166.map Block.length).sum = 32 := by
  simp [group166,dataT29Column2Block553,dataT29Column2Block554,dataT29Column2Block555,dataT29Column2Block556,dataT29Column2Block557,dataT29Column2Block558,dataT29Column2Block559,dataT29Column2Block560,Block.length]

theorem checked166 : checkBlocks (fun n => n/512 ^^^ n%512) 87712 group166 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group167 : List Block := [dataT29Column2Block561,dataT29Column2Block562,dataT29Column2Block563,dataT29Column2Block564,dataT29Column2Block565,dataT29Column2Block566,dataT29Column2Block567,dataT29Column2Block568]

theorem length167 : (group167.map Block.length).sum = 32 := by
  simp [group167,dataT29Column2Block561,dataT29Column2Block562,dataT29Column2Block563,dataT29Column2Block564,dataT29Column2Block565,dataT29Column2Block566,dataT29Column2Block567,dataT29Column2Block568,Block.length]

theorem checked167 : checkBlocks (fun n => n/512 ^^^ n%512) 87744 group167 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
