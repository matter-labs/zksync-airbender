import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData28

namespace Airbender.Blake2Worker.Xor7Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group16 : List Block := [dataT28Column2Block365,dataT28Column2Block366,dataT28Column2Block367,dataT28Column2Block368,dataT28Column2Block369,dataT28Column2Block370,dataT28Column2Block371,dataT28Column2Block372,dataT28Column2Block373,dataT28Column2Block374,dataT28Column2Block375,dataT28Column2Block376,dataT28Column2Block377,dataT28Column2Block378,dataT28Column2Block379,dataT28Column2Block380]

theorem length16 : (group16.map Block.length).sum = 2048 := by
  simp [group16,dataT28Column2Block365,dataT28Column2Block366,dataT28Column2Block367,dataT28Column2Block368,dataT28Column2Block369,dataT28Column2Block370,dataT28Column2Block371,dataT28Column2Block372,dataT28Column2Block373,dataT28Column2Block374,dataT28Column2Block375,dataT28Column2Block376,dataT28Column2Block377,dataT28Column2Block378,dataT28Column2Block379,dataT28Column2Block380,Block.length]

theorem checked16 : checkBlocks (fun n => n/128 ^^^ n%128) 13696 group16 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group17 : List Block := [dataT28Column2Block381,dataT28Column2Block382,dataT28Column2Block383,dataT28Column2Block384,dataT28Column2Block385]

theorem length17 : (group17.map Block.length).sum = 640 := by
  simp [group17,dataT28Column2Block381,dataT28Column2Block382,dataT28Column2Block383,dataT28Column2Block384,dataT28Column2Block385,Block.length]

theorem checked17 : checkBlocks (fun n => n/128 ^^^ n%128) 15744 group17 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor7Certificate
