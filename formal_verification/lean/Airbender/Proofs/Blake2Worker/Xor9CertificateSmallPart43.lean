import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group204 : List Block := [dataT29Column2Block856,dataT29Column2Block857,dataT29Column2Block858,dataT29Column2Block859,dataT29Column2Block860,dataT29Column2Block861,dataT29Column2Block862,dataT29Column2Block863]

theorem length204 : (group204.map Block.length).sum = 512 := by
  simp [group204,dataT29Column2Block856,dataT29Column2Block857,dataT29Column2Block858,dataT29Column2Block859,dataT29Column2Block860,dataT29Column2Block861,dataT29Column2Block862,dataT29Column2Block863,Block.length]

theorem checked204 : checkBlocks (fun n => n/512 ^^^ n%512) 95680 group204 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group205 : List Block := [dataT29Column2Block864,dataT29Column2Block865,dataT29Column2Block866,dataT29Column2Block867,dataT29Column2Block868,dataT29Column2Block869,dataT29Column2Block870,dataT29Column2Block871]

theorem length205 : (group205.map Block.length).sum = 512 := by
  simp [group205,dataT29Column2Block864,dataT29Column2Block865,dataT29Column2Block866,dataT29Column2Block867,dataT29Column2Block868,dataT29Column2Block869,dataT29Column2Block870,dataT29Column2Block871,Block.length]

theorem checked205 : checkBlocks (fun n => n/512 ^^^ n%512) 96192 group205 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group206 : List Block := [dataT29Column2Block872,dataT29Column2Block873,dataT29Column2Block874,dataT29Column2Block875,dataT29Column2Block876,dataT29Column2Block877,dataT29Column2Block878,dataT29Column2Block879]

theorem length206 : (group206.map Block.length).sum = 512 := by
  simp [group206,dataT29Column2Block872,dataT29Column2Block873,dataT29Column2Block874,dataT29Column2Block875,dataT29Column2Block876,dataT29Column2Block877,dataT29Column2Block878,dataT29Column2Block879,Block.length]

theorem checked206 : checkBlocks (fun n => n/512 ^^^ n%512) 96704 group206 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group207 : List Block := [dataT29Column2Block880,dataT29Column2Block881,dataT29Column2Block882,dataT29Column2Block883,dataT29Column2Block884,dataT29Column2Block885,dataT29Column2Block886,dataT29Column2Block887]

theorem length207 : (group207.map Block.length).sum = 512 := by
  simp [group207,dataT29Column2Block880,dataT29Column2Block881,dataT29Column2Block882,dataT29Column2Block883,dataT29Column2Block884,dataT29Column2Block885,dataT29Column2Block886,dataT29Column2Block887,Block.length]

theorem checked207 : checkBlocks (fun n => n/512 ^^^ n%512) 97216 group207 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
