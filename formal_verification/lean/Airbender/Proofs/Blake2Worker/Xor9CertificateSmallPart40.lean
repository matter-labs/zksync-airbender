import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group192 : List Block := [dataT29Column2Block760,dataT29Column2Block761,dataT29Column2Block762,dataT29Column2Block763,dataT29Column2Block764,dataT29Column2Block765,dataT29Column2Block766,dataT29Column2Block767]

theorem length192 : (group192.map Block.length).sum = 128 := by
  simp [group192,dataT29Column2Block760,dataT29Column2Block761,dataT29Column2Block762,dataT29Column2Block763,dataT29Column2Block764,dataT29Column2Block765,dataT29Column2Block766,dataT29Column2Block767,Block.length]

theorem checked192 : checkBlocks (fun n => n/512 ^^^ n%512) 89968 group192 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group193 : List Block := [dataT29Column2Block768,dataT29Column2Block769,dataT29Column2Block770,dataT29Column2Block771,dataT29Column2Block772,dataT29Column2Block773,dataT29Column2Block774,dataT29Column2Block775]

theorem length193 : (group193.map Block.length).sum = 464 := by
  simp [group193,dataT29Column2Block768,dataT29Column2Block769,dataT29Column2Block770,dataT29Column2Block771,dataT29Column2Block772,dataT29Column2Block773,dataT29Column2Block774,dataT29Column2Block775,Block.length]

theorem checked193 : checkBlocks (fun n => n/512 ^^^ n%512) 90096 group193 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group194 : List Block := [dataT29Column2Block776,dataT29Column2Block777,dataT29Column2Block778,dataT29Column2Block779,dataT29Column2Block780,dataT29Column2Block781,dataT29Column2Block782,dataT29Column2Block783]

theorem length194 : (group194.map Block.length).sum = 512 := by
  simp [group194,dataT29Column2Block776,dataT29Column2Block777,dataT29Column2Block778,dataT29Column2Block779,dataT29Column2Block780,dataT29Column2Block781,dataT29Column2Block782,dataT29Column2Block783,Block.length]

theorem checked194 : checkBlocks (fun n => n/512 ^^^ n%512) 90560 group194 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group195 : List Block := [dataT29Column2Block784,dataT29Column2Block785,dataT29Column2Block786,dataT29Column2Block787,dataT29Column2Block788,dataT29Column2Block789,dataT29Column2Block790,dataT29Column2Block791]

theorem length195 : (group195.map Block.length).sum = 512 := by
  simp [group195,dataT29Column2Block784,dataT29Column2Block785,dataT29Column2Block786,dataT29Column2Block787,dataT29Column2Block788,dataT29Column2Block789,dataT29Column2Block790,dataT29Column2Block791,Block.length]

theorem checked195 : checkBlocks (fun n => n/512 ^^^ n%512) 91072 group195 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
