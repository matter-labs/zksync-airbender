import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group148 : List Block := [dataT29Column2Block416,dataT29Column2Block417,dataT29Column2Block418,dataT29Column2Block419,dataT29Column2Block420,dataT29Column2Block421,dataT29Column2Block422,dataT29Column2Block423]

theorem length148 : (group148.map Block.length).sum = 64 := by
  simp [group148,dataT29Column2Block416,dataT29Column2Block417,dataT29Column2Block418,dataT29Column2Block419,dataT29Column2Block420,dataT29Column2Block421,dataT29Column2Block422,dataT29Column2Block423,Block.length]

theorem checked148 : checkBlocks (fun n => n/512 ^^^ n%512) 86272 group148 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group149 : List Block := [dataT29Column2Block424,dataT29Column2Block425,dataT29Column2Block426,dataT29Column2Block427,dataT29Column2Block428,dataT29Column2Block429,dataT29Column2Block430,dataT29Column2Block431]

theorem length149 : (group149.map Block.length).sum = 64 := by
  simp [group149,dataT29Column2Block424,dataT29Column2Block425,dataT29Column2Block426,dataT29Column2Block427,dataT29Column2Block428,dataT29Column2Block429,dataT29Column2Block430,dataT29Column2Block431,Block.length]

theorem checked149 : checkBlocks (fun n => n/512 ^^^ n%512) 86336 group149 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group150 : List Block := [dataT29Column2Block432,dataT29Column2Block433,dataT29Column2Block434,dataT29Column2Block435,dataT29Column2Block436,dataT29Column2Block437,dataT29Column2Block438,dataT29Column2Block439]

theorem length150 : (group150.map Block.length).sum = 64 := by
  simp [group150,dataT29Column2Block432,dataT29Column2Block433,dataT29Column2Block434,dataT29Column2Block435,dataT29Column2Block436,dataT29Column2Block437,dataT29Column2Block438,dataT29Column2Block439,Block.length]

theorem checked150 : checkBlocks (fun n => n/512 ^^^ n%512) 86400 group150 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group151 : List Block := [dataT29Column2Block440,dataT29Column2Block441,dataT29Column2Block442,dataT29Column2Block443,dataT29Column2Block444,dataT29Column2Block445,dataT29Column2Block446,dataT29Column2Block447]

theorem length151 : (group151.map Block.length).sum = 64 := by
  simp [group151,dataT29Column2Block440,dataT29Column2Block441,dataT29Column2Block442,dataT29Column2Block443,dataT29Column2Block444,dataT29Column2Block445,dataT29Column2Block446,dataT29Column2Block447,Block.length]

theorem checked151 : checkBlocks (fun n => n/512 ^^^ n%512) 86464 group151 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
