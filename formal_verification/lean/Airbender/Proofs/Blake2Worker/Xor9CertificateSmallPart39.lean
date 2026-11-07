import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group188 : List Block := [dataT29Column2Block728,dataT29Column2Block729,dataT29Column2Block730,dataT29Column2Block731,dataT29Column2Block732,dataT29Column2Block733,dataT29Column2Block734,dataT29Column2Block735]

theorem length188 : (group188.map Block.length).sum = 128 := by
  simp [group188,dataT29Column2Block728,dataT29Column2Block729,dataT29Column2Block730,dataT29Column2Block731,dataT29Column2Block732,dataT29Column2Block733,dataT29Column2Block734,dataT29Column2Block735,Block.length]

theorem checked188 : checkBlocks (fun n => n/512 ^^^ n%512) 89456 group188 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group189 : List Block := [dataT29Column2Block736,dataT29Column2Block737,dataT29Column2Block738,dataT29Column2Block739,dataT29Column2Block740,dataT29Column2Block741,dataT29Column2Block742,dataT29Column2Block743]

theorem length189 : (group189.map Block.length).sum = 128 := by
  simp [group189,dataT29Column2Block736,dataT29Column2Block737,dataT29Column2Block738,dataT29Column2Block739,dataT29Column2Block740,dataT29Column2Block741,dataT29Column2Block742,dataT29Column2Block743,Block.length]

theorem checked189 : checkBlocks (fun n => n/512 ^^^ n%512) 89584 group189 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group190 : List Block := [dataT29Column2Block744,dataT29Column2Block745,dataT29Column2Block746,dataT29Column2Block747,dataT29Column2Block748,dataT29Column2Block749,dataT29Column2Block750,dataT29Column2Block751]

theorem length190 : (group190.map Block.length).sum = 128 := by
  simp [group190,dataT29Column2Block744,dataT29Column2Block745,dataT29Column2Block746,dataT29Column2Block747,dataT29Column2Block748,dataT29Column2Block749,dataT29Column2Block750,dataT29Column2Block751,Block.length]

theorem checked190 : checkBlocks (fun n => n/512 ^^^ n%512) 89712 group190 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group191 : List Block := [dataT29Column2Block752,dataT29Column2Block753,dataT29Column2Block754,dataT29Column2Block755,dataT29Column2Block756,dataT29Column2Block757,dataT29Column2Block758,dataT29Column2Block759]

theorem length191 : (group191.map Block.length).sum = 128 := by
  simp [group191,dataT29Column2Block752,dataT29Column2Block753,dataT29Column2Block754,dataT29Column2Block755,dataT29Column2Block756,dataT29Column2Block757,dataT29Column2Block758,dataT29Column2Block759,Block.length]

theorem checked191 : checkBlocks (fun n => n/512 ^^^ n%512) 89840 group191 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
