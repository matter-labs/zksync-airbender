import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group200 : List Block := [dataT29Column2Block824,dataT29Column2Block825,dataT29Column2Block826,dataT29Column2Block827,dataT29Column2Block828,dataT29Column2Block829,dataT29Column2Block830,dataT29Column2Block831]

theorem length200 : (group200.map Block.length).sum = 512 := by
  simp [group200,dataT29Column2Block824,dataT29Column2Block825,dataT29Column2Block826,dataT29Column2Block827,dataT29Column2Block828,dataT29Column2Block829,dataT29Column2Block830,dataT29Column2Block831,Block.length]

theorem checked200 : checkBlocks (fun n => n/512 ^^^ n%512) 93632 group200 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group201 : List Block := [dataT29Column2Block832,dataT29Column2Block833,dataT29Column2Block834,dataT29Column2Block835,dataT29Column2Block836,dataT29Column2Block837,dataT29Column2Block838,dataT29Column2Block839]

theorem length201 : (group201.map Block.length).sum = 512 := by
  simp [group201,dataT29Column2Block832,dataT29Column2Block833,dataT29Column2Block834,dataT29Column2Block835,dataT29Column2Block836,dataT29Column2Block837,dataT29Column2Block838,dataT29Column2Block839,Block.length]

theorem checked201 : checkBlocks (fun n => n/512 ^^^ n%512) 94144 group201 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group202 : List Block := [dataT29Column2Block840,dataT29Column2Block841,dataT29Column2Block842,dataT29Column2Block843,dataT29Column2Block844,dataT29Column2Block845,dataT29Column2Block846,dataT29Column2Block847]

theorem length202 : (group202.map Block.length).sum = 512 := by
  simp [group202,dataT29Column2Block840,dataT29Column2Block841,dataT29Column2Block842,dataT29Column2Block843,dataT29Column2Block844,dataT29Column2Block845,dataT29Column2Block846,dataT29Column2Block847,Block.length]

theorem checked202 : checkBlocks (fun n => n/512 ^^^ n%512) 94656 group202 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group203 : List Block := [dataT29Column2Block848,dataT29Column2Block849,dataT29Column2Block850,dataT29Column2Block851,dataT29Column2Block852,dataT29Column2Block853,dataT29Column2Block854,dataT29Column2Block855]

theorem length203 : (group203.map Block.length).sum = 512 := by
  simp [group203,dataT29Column2Block848,dataT29Column2Block849,dataT29Column2Block850,dataT29Column2Block851,dataT29Column2Block852,dataT29Column2Block853,dataT29Column2Block854,dataT29Column2Block855,Block.length]

theorem checked203 : checkBlocks (fun n => n/512 ^^^ n%512) 95168 group203 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
