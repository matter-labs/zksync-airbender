import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group220 : List Block := [dataT29Column2Block918,dataT29Column2Block919]

theorem length220 : (group220.map Block.length).sum = 512 := by
  simp [group220,dataT29Column2Block918,dataT29Column2Block919,Block.length]

theorem checked220 : checkBlocks (fun n => n/512 ^^^ n%512) 103680 group220 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group221 : List Block := [dataT29Column2Block920,dataT29Column2Block921]

theorem length221 : (group221.map Block.length).sum = 512 := by
  simp [group221,dataT29Column2Block920,dataT29Column2Block921,Block.length]

theorem checked221 : checkBlocks (fun n => n/512 ^^^ n%512) 104192 group221 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group222 : List Block := [dataT29Column2Block922,dataT29Column2Block923]

theorem length222 : (group222.map Block.length).sum = 512 := by
  simp [group222,dataT29Column2Block922,dataT29Column2Block923,Block.length]

theorem checked222 : checkBlocks (fun n => n/512 ^^^ n%512) 104704 group222 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group223 : List Block := [dataT29Column2Block924,dataT29Column2Block925]

theorem length223 : (group223.map Block.length).sum = 512 := by
  simp [group223,dataT29Column2Block924,dataT29Column2Block925,Block.length]

theorem checked223 : checkBlocks (fun n => n/512 ^^^ n%512) 105216 group223 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
