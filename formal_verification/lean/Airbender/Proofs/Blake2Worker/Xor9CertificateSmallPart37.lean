import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group180 : List Block := [dataT29Column2Block664,dataT29Column2Block665,dataT29Column2Block666,dataT29Column2Block667,dataT29Column2Block668,dataT29Column2Block669,dataT29Column2Block670,dataT29Column2Block671]

theorem length180 : (group180.map Block.length).sum = 128 := by
  simp [group180,dataT29Column2Block664,dataT29Column2Block665,dataT29Column2Block666,dataT29Column2Block667,dataT29Column2Block668,dataT29Column2Block669,dataT29Column2Block670,dataT29Column2Block671,Block.length]

theorem checked180 : checkBlocks (fun n => n/512 ^^^ n%512) 88432 group180 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group181 : List Block := [dataT29Column2Block672,dataT29Column2Block673,dataT29Column2Block674,dataT29Column2Block675,dataT29Column2Block676,dataT29Column2Block677,dataT29Column2Block678,dataT29Column2Block679]

theorem length181 : (group181.map Block.length).sum = 128 := by
  simp [group181,dataT29Column2Block672,dataT29Column2Block673,dataT29Column2Block674,dataT29Column2Block675,dataT29Column2Block676,dataT29Column2Block677,dataT29Column2Block678,dataT29Column2Block679,Block.length]

theorem checked181 : checkBlocks (fun n => n/512 ^^^ n%512) 88560 group181 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group182 : List Block := [dataT29Column2Block680,dataT29Column2Block681,dataT29Column2Block682,dataT29Column2Block683,dataT29Column2Block684,dataT29Column2Block685,dataT29Column2Block686,dataT29Column2Block687]

theorem length182 : (group182.map Block.length).sum = 128 := by
  simp [group182,dataT29Column2Block680,dataT29Column2Block681,dataT29Column2Block682,dataT29Column2Block683,dataT29Column2Block684,dataT29Column2Block685,dataT29Column2Block686,dataT29Column2Block687,Block.length]

theorem checked182 : checkBlocks (fun n => n/512 ^^^ n%512) 88688 group182 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group183 : List Block := [dataT29Column2Block688,dataT29Column2Block689,dataT29Column2Block690,dataT29Column2Block691,dataT29Column2Block692,dataT29Column2Block693,dataT29Column2Block694,dataT29Column2Block695]

theorem length183 : (group183.map Block.length).sum = 128 := by
  simp [group183,dataT29Column2Block688,dataT29Column2Block689,dataT29Column2Block690,dataT29Column2Block691,dataT29Column2Block692,dataT29Column2Block693,dataT29Column2Block694,dataT29Column2Block695,Block.length]

theorem checked183 : checkBlocks (fun n => n/512 ^^^ n%512) 88816 group183 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
